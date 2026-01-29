# Code-Level TLA+ Specification for etcd/raft Core Module

This directory contains a code-level TLA+ specification for the etcd/raft library, along with tooling for trace validation and model checking.

## Overview

The specification models the core Raft algorithm as implemented in etcd/raft, including:

- **Leader election** - RequestVote handling, term management
- **Log replication** - AppendEntries, log matching, commitment
- **Membership reconfiguration** - Joint consensus, ConfChangeV2, single-node changes
- **Snapshot** - Snapshot sending/receiving, log compaction
- **Progress tracking** - StateProbe, StateReplicate, StateSnapshot, Inflights
- **Flow control** - MsgAppFlowPaused, MaxInflightMsgs

## Directory Structure

```
tla-extended/
├── etcdraft.tla          # Main TLA+ specification
├── etcdraft.cfg          # Base TLC configuration
├── MCetcdraft.tla        # Model checking configuration
├── MCetcdraft.cfg        # TLC model checking settings
├── Traceetcdraft.tla     # Trace validation specification
├── Traceetcdraft.cfg     # Trace validation settings
├── harness/              # Go test harness for trace generation
│   ├── main.go           # Harness entry point
│   ├── parser.go         # Trace parser
│   └── rawnode_access.go # RawNode accessor
├── patches/              # Instrumentation patches
│   └── instrumentation.patch
└── traces/               # 37 trace files covering various scenarios
    ├── basic.ndjson
    ├── confchange_*.ndjson    # Configuration change scenarios
    ├── snapshot_*.ndjson      # Snapshot scenarios
    └── ...
```

## Requirements

- Java 11+ (for TLC model checker)
- [tla2tools.jar](https://github.com/tlaplus/tlaplus/releases)
- [CommunityModules-deps.jar](https://github.com/tlaplus/CommunityModules/releases)

## Trace Validation

### 1. Apply Instrumentation Patch

```bash
cd /path/to/raft
git apply tla-extended/patches/instrumentation.patch
```

### 2. Generate Traces

Build and run the harness to generate traces from raft tests:

```bash
cd tla-extended/harness
go build -o harness .
./harness -test TestBasic -output ../traces/
```

### 3. Validate Traces

Use `validate.sh` to validate traces in batch:

```bash
cd tla-extended
./validate.sh \
    -s Traceetcdraft.tla \
    -c Traceetcdraft.cfg \
    traces/*.ndjson
```

By default, `validate.sh` uses all CPU cores. Use `-p <num>` to limit concurrency.

## Trace Validation Coverage

The specification has been validated against 37 traces generated from etcd/raft's test suite:

| Metric | Value |
|--------|-------|
| Total statements | 431 |
| Covered statements | 407 |
| Coverage | **94.43%** |

The uncovered statements (5.57%) represent edge cases that require strict timing sequences to trigger. The current test harness cannot generate such scenarios, as they involve specific interleavings that are difficult to produce through standard testing. Future improvements to the harness could potentially increase coverage.

## Invariants

The specification defines **96 invariants** organized into 8 categories, derived from 3 sources:

### Sources

| Source | Description |
|--------|-------------|
| **Raft Paper** | Safety properties from the Raft consensus paper |
| **Code** | Invariants derived from etcd/raft implementation details |
| **Issue/Bug** | Regression tests for historical bugs from git history |

### Categories

| Category | Count | Description | Example Invariants |
|----------|-------|-------------|-------------------|
| **Progress** | 24 | Progress tracking, Inflights, flow control | `ProbeLimitInv`, `ReplicatePauseInv`, `InflightsLogIndexInv` |
| **Log** | 12 | Log structure, matching, indexing | `LogMatchingInv`, `LogStructureInv`, `LeaderLogLengthInv` |
| **Message** | 18 | Message validity, endpoints, content | `MessageIndexValidInv`, `AppendEntriesCommitBoundInv` |
| **Snapshot** | 14 | Snapshot state, consistency | `SnapshotInflightsInv`, `SnapshotTermValidInv` |
| **Election** | 10 | Leader election, voting | `MoreThanOneLeaderInv`, `VotesGrantedSubsetInv` |
| **Config** | 8 | Configuration, joint consensus | `JointConfigNonEmptyInv`, `ConfigurationInv` |
| **Term** | 6 | Term validity, consistency | `TermPositiveInv`, `LeaderTermPositiveInv` |
| **Durable** | 4 | Durability, commitment | `CommittedIsDurableInv`, `AppliedBoundInv` |

### Key Safety Invariants (from Raft Paper)

- **MoreThanOneLeaderInv** - At most one leader per term
- **LogMatchingInv** - If two logs contain an entry with the same index and term, the logs are identical in all preceding entries
- **LeaderCompletenessInv** - If an entry is committed, it will be present in the logs of all future leaders
- **QuorumLogInv** - Committed entries exist on a quorum of servers

### Bug Detection Invariants (from Issue/Bug)

- **AppendEntriesPrevLogTermValidInv** - Prevents bug 76f1249 (panic on log truncation)
- **SinglePendingLeaveJointInv** - Prevents bug bd3c759 (multiple auto-leave attempts)
- **ProbeNetworkMessageLimitInv** - Detects flow control issues in StateProbe

## Model Checking (Simulation)

For quick exploration via simulation:

```bash
java -XX:+UseParallelGC \
    -cp tla2tools.jar:CommunityModules-deps.jar \
    tlc2.TLC \
    -config MCetcdraft.cfg \
    MCetcdraft.tla \
    -simulate \
    -depth 100
```

## References

- [etcd/raft documentation](https://pkg.go.dev/go.etcd.io/raft/v3)
- [Raft paper](https://raft.github.io/raft.pdf)
- [TLA+ documentation](https://lamport.azurewebsites.net/tla/tla.html)
