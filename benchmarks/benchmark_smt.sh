#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="SinglePrefix/FAT4/sp4.nv
SinglePrefix/FAT4/fat4Pol.nv
SinglePrefix/FAT8/sp8.nv
SinglePrefix/FAT8/fat8Pol.nv
SinglePrefix/FAT10/sp10.nv
SinglePrefix/FAT10/fat10Pol.nv
SinglePrefix/FAT12/sp12.nv
SinglePrefix/FAT12/fat12Pol.nv"

for file in $BENCHMARKS
do
    time "$NV" -m "$file";
    echo "\n";
done
