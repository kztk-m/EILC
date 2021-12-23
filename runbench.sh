#!/bin/sh 
set -x

dobench(){
    BNAME=$1 
    FNAME=`date -j "+$BNAME-%Y-%m-%dT%H%M.html"`
    stack bench embedding-ilc:bench:$BNAME --flag embedding-ilc:dump --ba "--output benchmark_results/$FNAME"
}

case "$1" in
    "tree") 
        dobench "tree" 
        ;;
    "sequence") 
        dobench "sequence" 
        ;;
    *)
        dobench "tree" 
        dobench "sequence" 
        ;;
esac 