#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="FaultTolerance/SinglePrefix/USCarrierOneLink.nv
FaultTolerance/SinglePrefix/fat12polOneLink.nv
FaultTolerance/SinglePrefix/fat16polOneLink.nv
FaultTolerance/SinglePrefix/fat20polOneLink.nv"

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
