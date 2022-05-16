#!/usr/bin/env bash
# NOTE: not posix shell compliant
# Print an all-tor benchmark based on the given single-prefix benchmark.
INPUT=$1
NPODS=$2

# get all references to edge layer nodes
tors=$(rg -No -e 'edge-(\d*)=\d*' -r '$1' "$INPUT")
require="require (match (d, pod) with"
ncores=$(( (NPODS / 2) * (NPODS / 2)))
for tor in $tors; do
    # this is the same brittle and dangerous prefix generation
    # that topoconfig.py uses, so this may break!!!
    # construct an integer equivalent to a 70._._.0 address
    addr=$((tor * 256 + 70 * 256 * 256 * 256))
    # fattree nodes are labelled as follows:
    # [0,(pods/2)**2): core nodes
    # [(pods/2)**2,(pods/2)**2+(pods/2)): agg nodes for pod 0
    # [(pods/2)**2+(pods/2),(pods/2)**2+pods): edge nodes for pod 0
    # and repeating by (pods/2) increments for subsequent pods
    if [ "$tor" -lt $ncores ]; then
        pod=$NPODS
    else
        pod=$(( (tor - ncores) / NPODS))
    fi
    branch=$(printf " | ((%d, 24u6), %d) -> true" $addr $pod)
    require="${require}\n${branch}"
done
require="${require}\n | _ -> false)"

# change d to a symbolic and remove test on d's value from assert_node
# two versions, depending on if d is written in prefix form or tuple form
sed -e 's/let d = (70.[0-9]*.[0-9]*.0\/24u6)/symbolic d : (int, int6)\nsymbolic pod : int/' \
    -e 's/let d = ([0-9]*, 24u6)/symbolic d : (int, int6)\nsymbolic pod : int/' \
    -e 's/  if (d = (70.[0-9]*.[0-9]*.0\/24u6)) then/  if true then/' \
    -e 's/  if (d = ([0-9]*, 24u6)) then/  if true then/' \
    "$INPUT"
# add the require clause
echo -e "$require"
