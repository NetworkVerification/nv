# Benchmarks

These NV files are translated from actual configurations.
The folder structure describes the following:
* AllPrefixes - Models ALL prefixes simultaneously, use for simulator.
* SinglePrefix - Models any single prefix, use mainly for SMT.
* FaultTolerance - Link/Node fault tolerance analyses based on BDDs

## Networks:
- FatTrees: Files with pol in the filename denote fat trees with a policy of
  dropping routes after more than one up-down-up between layers in the fat tree. 
- USCarrier: USCarrier is a network from topology zoo with policy synthesized
  using netcomplete.
