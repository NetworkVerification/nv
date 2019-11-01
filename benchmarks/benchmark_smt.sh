#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="SinglePrefix/FAT4/sp4.nv
SinglePrefix/FAT4/fat4pol.nv
SinglePrefix/FAT8/sp8.nv
SinglePrefix/FAT8/fat8pol.nv
SinglePrefix/FAT10/sp10.nv
SinglePrefix/FAT10/fat10pol.nv
SinglePrefix/FAT12/sp12.nv
SinglePrefix/FAT12/fat12pol.nv"

for file in $BENCHMARKS
do
    time "$NV" -m "$file";
    echo "\n";
done
