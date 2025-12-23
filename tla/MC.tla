---- MODULE MC ----
\* Model Checking configuration for etcdraft_progress
\* Defines symmetry sets and model-specific configurations

EXTENDS etcdraft_progress, TLC

\* Symmetry sets for both servers and values
\* All servers are symmetric - permuting them produces equivalent states
\* All values are symmetric - permuting them produces equivalent states
Symmetry == Permutations(Server) \union Permutations(Values)

====
