#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="FaultTolerance/SinglePrefix/sp8OneLink.nv
FaultTolerance/SinglePrefix/sp10OneLink.nv
FaultTolerance/SinglePrefix/sp12OneLink.nv
FaultTolerance/SinglePrefix/fat12PolOneLink.nv"

SMT_BENCHMARKS="SinglePrefix/FAT8/sp8.nv
SinglePrefix/FAT10/sp10.nv
SinglePrefix/FAT12/sp12.nv
SinglePrefix/FAT12/fat12Pol.nv"

for file in $BENCHMARKS
do
    time "$NV" -inline -compile "$file";
    echo "\n";
done

#for file in $SMT_BENCHMARKS
#do
#    time "$NV" -smt -link-failures 1 "$file";
#    echo "\n";
#done
