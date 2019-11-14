#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="AllPrefixes/FAT20/fat20PolSim.nv"

for file in $BENCHMARKS
do
    time "$NV" -inline -compile "$file";
    echo "\n";
done
