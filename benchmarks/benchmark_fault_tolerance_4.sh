#!/usr/bin/env bash
# Comparing the performance of interpreted vs native simulator and single-pre vs all-pre fault tolerance analysis.

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="FaultTolerance/SinglePrefix/sp16OneLink.nv
FaultTolerance/AllPrefixes/sp16SimOneLink.nv
FaultTolerance/SinglePrefix/fat16PolOneLink.nv
FaultTolerance/AllPrefixes/fat16PolSimOneLink.nv"

for file in $BENCHMARKS
do
    time "$NV" -inline -simulate "$file";
    echo "\n";
done

for file in $BENCHMARKS
do
    time "$NV" -inline -compile "$file";
    echo "\n";
done
