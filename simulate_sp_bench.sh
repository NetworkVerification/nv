#!/bin/bash

# get the solutions to the original spX.nv program (for use when coming up with invariants)
SP=$1

./nv -v -s $SP |\
  # shave off everything after aslen
  cut -d';' -f 1 |\
  # delete the non-label lines
  sed -e '/^[^\(Label\)]/d' |\
  # simplify to just the node number and the corresponding distance
  sed -e 's/Label(\([0-9]*\)):{  bgp= Some({  aslen= \([0-9]\)u32/L(\1): \2/g' |\
  # sort by the second column
  sort -k2 -n
