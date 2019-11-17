#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="AllPrefixes/FAT20/fat20PolSim.nv
AllPrefixes/FAT24/fat24PolSim.nv
AllPrefixes/FAT28/fat28PolSim.nv
AllPrefixes/FAT32/fat32PolSim.nv"

for file in $BENCHMARKS
do
    time "$NV" -compile "$file";
    echo "\n";
done