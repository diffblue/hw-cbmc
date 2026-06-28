#!/bin/sh

# abort on error
set -e

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)

# clone sv-tests repo if not done yet
if [ ! -e sv-tests/.git ] ; then
  git clone https://github.com/chipsalliance/sv-tests
  (cd sv-tests && git checkout cbe02cf550b1345f5b75fee0c85145b1b68f379e)
fi

# install Python dependencies needed by the runner
pip3 install psutil

# copy the ebmc runner
cp "$SCRIPT_DIR/ebmc.py" sv-tests/tools/runners/

cd sv-tests

# run the sv-tests
make tests
