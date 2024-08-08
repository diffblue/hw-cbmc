#!/bin/sh

# abort on error
set -e

# clone Hazard3 repo if not done yet
if [ ! -e Hazard3/.git ] ; then
  git clone https://github.com/Wren6991/Hazard3
  git checkout v1.0
fi

cd Hazard3

ebmc -I hdl -D HAZARD3_ASSERTIONS --bound 0 hdl/arith/hazard3_shift_barrel.v
