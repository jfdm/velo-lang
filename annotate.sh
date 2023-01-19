#!/bin/env bash

test ! -z $1 && set -x # Show commands if first arg is non-zero

mkdir -p build/html

katla_run()
{
    KATLA_EXE=$(which katla)
    test -x KATLA_EXE && echo "Katla not installed"
    test -z $2 && echo "missing ttm"
    FOUT=$4
    DOUT=${FOUT%/*} # equiv to dirname
    mkdir -p "$DOUT"
    echo "Generating $4"
    $KATLA_EXE "$1" "$2" "$3" > "$4"
}

find src -type f -iname "*.idr" -print0 |\
    while IFS= read -r -d '' file; do
        FILE_LOCAL=${file#src/} # remove prefix
        FILE_ttm=${FILE_LOCAL%idr}ttm
        FILE_html=${FILE_LOCAL%idr}html
        katla_run html "./${file}" ./build/ttc/*/"${FILE_ttm}" "./build/html/${FILE_html}"
    done

# -- [ EOF ]
