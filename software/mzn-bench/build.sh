#!/bin/bash

MZN_PATH="../minizinc"

cmake -B "$MZN_PATH/release" -S $MZN_PATH 
cmake --build "$MZN_PATH/release"
minizinc --solvers

cmake -DCMAKE_BUILD_TYPE=Debug -B "$MZN_PATH/build" -S $MZN_PATH 
cmake --build "$MZN_PATH/build"
minizinc --solvers


# build open-wbo
cd ../minizinc/share/minizinc/open-wbo/
make r
