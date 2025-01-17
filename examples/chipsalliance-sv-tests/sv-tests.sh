#!/bin/sh

# abort on error
set -e

# clone sv-tests repo if not done yet
if [ ! -e sv-tests/.git ] ; then
  git clone https://github.com/chipsalliance/sv-tests
  git checkout cbe02cf550b1345f5b75fee0c85145b1b68f379e
fi

cd sv-tests

