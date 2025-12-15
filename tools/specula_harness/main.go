package main

import (
	"errors"
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"runtime"
	rt "runtime/trace"
	"strings"
	"testing"
	"time"

	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/rafttest"
)

type scenarioResolution struct {
	Name string
	Path string
}

type runConfig struct {
	Scenario       scenarioResolution
	TraceOut       string
	RuntimeTrace   string
	MetadataOut    string
	Verbose        bool
	PrintScenario  bool
	SkipValidation bool
}

func main() {
	cfg := parseFlags()

	if cfg.PrintScenario {
		if err := listScenarios(); err != nil {
			log.Fatalf("list scenarios: %v", err)
		}
		return
	}

	if err := run(cfg); err != nil {
		log.Fatalf("specula harness failed: %v", err)
	}
}

func parseFlags() runConfig {
	var (
		scenarioFlag     = flag.String("scenario", "basic_election", "Scenario name or path to a datadriven script.")
		traceOutFlag     = flag.String("out", "", "Path to NDJSON state trace output (defaults to traces/<scenario>.ndjson).")
		runtimeTraceFlag = flag.String("runtime-trace", "", "Optional Go runtime trace output (.out).")
		metadataFlag     = flag.String("meta", "", "Optional metadata sidecar path (defaults to <out>.meta.json).")
		listFlag         = flag.Bool("list", false, "List built-in scenarios and exit.")
		verboseFlag      = flag.Bool("verbose", false, "Print scenario handler output while running.")
		skipValidateFlag = flag.Bool("skip-validate", false, "Skip comparing handler output against expected blocks.")
	)
	flag.Parse()

	resolution, err := resolveScenario(*scenarioFlag)
	if err != nil {
		log.Fatalf("resolve scenario: %v", err)
	}

	traceOut := *traceOutFlag
	if traceOut == "" {
		traceOut = filepath.Join("traces", resolution.Name+".ndjson")
	}
	metaOut := *metadataFlag
	if metaOut == "" {
		metaOut = traceOut + ".meta.json"
	}

	return runConfig{
		Scenario:       resolution,
		TraceOut:       traceOut,
		RuntimeTrace:   *runtimeTraceFlag,
		MetadataOut:    metaOut,
		Verbose:        *verboseFlag,
		PrintScenario:  *listFlag,
		SkipValidation: *skipValidateFlag,
	}
}

func run(cfg runConfig) error {
	directives, err := loadDirectives(cfg.Scenario.Path)
	if err != nil {
		return fmt.Errorf("load scenario: %w", err)
	}
	if len(directives) == 0 {
		return fmt.Errorf("scenario %q (%s) contained no directives", cfg.Scenario.Name, cfg.Scenario.Path)
	}

	tracer, closeTrace, err := newNDJSONLogger(cfg.TraceOut, cfg.Scenario.Name)
	if err != nil {
		return fmt.Errorf("open trace: %w", err)
	}
	defer func() {
		_ = closeTrace()
	}()

	env := rafttest.NewInteractionEnv(&rafttest.InteractionOpts{
		OnConfig: func(cfg *raft.Config) {
			cfg.TraceLogger = tracer
		},
		SetRandomizedElectionTimeout: func(node *raft.RawNode, timeout int) {
			if err := setRandomizedElectionTimeout(node, timeout); err != nil {
				log.Printf("set randomized election timeout: %v", err)
			}
		},
	})

	stopRuntimeTrace, err := startRuntimeTrace(cfg.RuntimeTrace)
	if err != nil {
		return err
	}
	if stopRuntimeTrace != nil {
		defer func() {
			_ = stopRuntimeTrace()
		}()
	}

	if !raft.StateTraceDeployed {
		log.Printf("warning: state trace hooks disabled (build without -tags=with_tla); NDJSON will be empty")
	}

	var tb testing.T
	start := time.Now()
	if err := runDirectives(&tb, env, directives, cfg.Verbose, cfg.SkipValidation); err != nil {
		return err
	}
	duration := time.Since(start)

	if err := writeMetadata(cfg.MetadataOut, HarnessMetadata{
		Scenario:     cfg.Scenario.Name,
		ScenarioPath: cfg.Scenario.Path,
		TraceOut:     cfg.TraceOut,
		RuntimeTrace: cfg.RuntimeTrace,
		GoVersion:    runtime.Version(),
		BuildTags:    []string{"with_tla"},
		DurationMS:   duration.Milliseconds(),
		GitSHA:       currentGitSHA(),
		GeneratedAt:  time.Now().UTC(),
	}); err != nil {
		return fmt.Errorf("write metadata: %w", err)
	}

	fmt.Printf("Scenario %q complete in %s\n", cfg.Scenario.Name, duration.Round(time.Millisecond))
	fmt.Printf("State trace: %s\n", cfg.TraceOut)
	if cfg.RuntimeTrace != "" {
		fmt.Printf("Runtime trace: %s\n", cfg.RuntimeTrace)
	}
	fmt.Printf("Metadata: %s\n", cfg.MetadataOut)
	return nil
}

func runDirectives(t *testing.T, env *rafttest.InteractionEnv, directives []directive, verbose bool, skipValidate bool) error {
	for _, td := range directives {
		output := env.Handle(t, td.TestData)
		if verbose && strings.TrimSpace(output) != "" {
			fmt.Printf("=== %s (%s)\n%s\n", td.Cmd, td.Pos, output)
		}

		if skipValidate || td.Expected == "" {
			continue
		}
		if strings.TrimSpace(td.Expected) != strings.TrimSpace(output) {
			return fmt.Errorf("output mismatch at %s\nexpected:\n%s\nactual:\n%s\n", td.Pos, td.Expected, output)
		}
	}
	return nil
}

func startRuntimeTrace(path string) (func() error, error) {
	if path == "" {
		return nil, nil
	}

	if err := mkdirAll(path); err != nil {
		return nil, fmt.Errorf("prepare runtime trace path: %w", err)
	}

	f, err := os.Create(path)
	if err != nil {
		return nil, fmt.Errorf("create runtime trace: %w", err)
	}

	if err := rt.Start(f); err != nil {
		_ = f.Close()
		return nil, fmt.Errorf("start runtime trace: %w", err)
	}

	return func() error {
		rt.Stop()
		return f.Close()
	}, nil
}

func resolveScenario(s string) (scenarioResolution, error) {
	if s == "" {
		return scenarioResolution{}, errors.New("scenario name or path is required")
	}

	if fi, err := os.Stat(s); err == nil && !fi.IsDir() {
		return scenarioResolution{Name: strings.TrimSuffix(filepath.Base(s), filepath.Ext(s)), Path: s}, nil
	}

	if path, ok := scenarioMap()[s]; ok {
		return scenarioResolution{Name: s, Path: path}, nil
	}

	alt := filepath.Join("testdata", s)
	if fi, err := os.Stat(alt); err == nil && !fi.IsDir() {
		return scenarioResolution{Name: strings.TrimSuffix(s, filepath.Ext(s)), Path: alt}, nil
	}

	return scenarioResolution{}, fmt.Errorf("unknown scenario %q (provide a path or use -list)", s)
}

func listScenarios() error {
	fmt.Println("Built-in scenarios:")
	for name, path := range scenarioMap() {
		fmt.Printf("  %s -> %s\n", name, path)
	}
	return nil
}

func scenarioMap() map[string]string {
	return map[string]string{
		"basic_election":        filepath.Join("testdata", "campaign.txt"),
		"confchange_add_remove": filepath.Join("testdata", "confchange_v2_add_single_auto.txt"),
		"leader_transfer":       filepath.Join("testdata", "confchange_v2_replace_leader.txt"),
		"async_storage_writes":  filepath.Join("testdata", "async_storage_writes.txt"),
		"snapshot_and_recovery": filepath.Join("testdata", "snapshot_succeed_via_app_resp.txt"),
		"partition_and_recover": filepath.Join("testdata", "replicate_pause.txt"),
		"forget_leader":         filepath.Join("testdata", "forget_leader.txt"),
	}
}
