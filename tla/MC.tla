---- MODULE MC ----
\* Model Checking configuration for etcdraft_progress
\* Defines symmetry sets and model-specific configurations

EXTENDS etcdraft_progress, TLC

\* Symmetry set for server nodes
\* All servers are symmetric - permuting them produces equivalent states
Symmetry == Permutations(Server)

====
