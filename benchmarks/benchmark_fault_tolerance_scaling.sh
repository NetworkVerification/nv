#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="
FaultTolerance/SinglePrefix/USCarrierOneLink.nv
FaultTolerance/SinglePrefix/USCarrierTwoLinks.nv
FaultTolerance/SinglePrefix/USCarrierThreeLinks.nv
FaultTolerance/SinglePrefix/fat12PolOneLink.nv
FaultTolerance/SinglePrefix/fat12PolTwoLinks.nv
FaultTolerance/SinglePrefix/fat12PolThreeLinks.nv
FaultTolerance/SinglePrefix/fat16PolOneLink.nv
FaultTolerance/SinglePrefix/fat16PolTwoLinks.nv
FaultTolerance/SinglePrefix/fat16PolThreeLinks.nv
FaultTolerance/SinglePrefix/fat20PolOneLink.nv
FaultTolerance/SinglePrefix/fat20PolTwoLinks.nv
FaultTolerance/SinglePrefix/fat20PolThreeLinks.nv
FaultTolerance/SinglePrefix/fat28PolOneLink.nv
FaultTolerance/SinglePrefix/fat28PolTwoLinks.nv"

for file in $BENCHMARKS
do
    time "$NV" -inline -compile "$file";
    echo "\n";
done
