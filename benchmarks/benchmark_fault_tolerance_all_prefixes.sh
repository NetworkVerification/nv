#!/usr/bin/env bash

#!/usr/bin/env bash

NV="../_build/default/src/exe/main.exe"
BENCHMARKS="
FaultTolerance/AllPrefixes/fat12PolSimOneLink.nv
FaultTolerance/AllPrefixes/fat16PolSimOneLink.nv"

for file in $BENCHMARKS
do
    /usr/bin/time -l "$NV" -inline -compile "$file";
    echo "\n";
done

for file in $BENCHMARKS
do
    /usr/bin/time -l "$NV" -inline -simulate "$file";
    echo "\n";
done
