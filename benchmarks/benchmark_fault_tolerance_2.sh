#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="FaultTolerance/SinglePrefix/sp16OneLink.nv
FaultTolerance/SinglePrefix/fat16PolOneLink.nv
FaultTolerance/AllPrefixes/sp16SimOneLink.nv
FaultTolerance/AllPrefixes/fat16PolSimOneLink.nv"


for file in $BENCHMARKS
do
    time "$NV" -inline -simulate "$file";
    echo "\n";
done

echo "\nRunning compiled tests\n"

for file in $BENCHMARKS
do
    time "$NV" -inline -compile "$file";
    echo "\n";
done
