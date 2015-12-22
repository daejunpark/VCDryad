#!/bin/bash

dir=`dirname $0`

[ $# -ge 2 ] || { echo "no input"; exit 1; }
gen=$1
bpl=$2

node $gen $bpl >$bpl.pred
node $dir/pred_inject.js $bpl $bpl.pred >$bpl.pred.bpl
