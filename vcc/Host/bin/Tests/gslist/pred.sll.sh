#!/bin/bash

dir=`dirname $0`

[ $# -ge 1 ] || { echo "no input"; exit 1; }
bpl=$1

node $dir/pred_gen.sll.js $bpl >$bpl.pred
node $dir/pred_inject.js $bpl $bpl.pred >$bpl.pred.bpl
dos2unix -q $bpl.pred.bpl
