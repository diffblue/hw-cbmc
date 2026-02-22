#!/bin/sh

# This runs ebmc in BMC mode on the HWMCC08 benchmarks.

if [ ! -e aiger/. ] ; then
  echo Downloading and building the AIGER tools at version 1.9.20
  git clone -b rel-1.9.20 https://github.com/arminbiere/aiger
  (cd aiger ; ./configure.sh ; make aigtosmv )
fi

if [ ! -e hwmcc08/. ] ; then
  echo Downloading HWMCC08 benchmark archive
  wget -q http://fmv.jku.at/hwmcc/hwmcc08public.tar.bz2
  bunzip2 hwmcc08public.tar.bz2
  tar xf hwmcc08public.tar
  rm hwmcc08public.tar
fi

if [ ! -e hwmcc08public-smv/. ] ; then
  echo Converting AIGER to SMV
  mkdir hwmcc08public-smv
  (cd hwmcc08; for FILE in *.aig ; do
    SMV=`echo "$FILE" | sed s/.aig/.smv/`
    ../aiger/aigtosmv -b "$FILE" "../hwmcc08public-smv/$SMV"
  done)
fi

# expected answers
# from the abc result column in https://fmv.jku.at/hwmcc08/hwmcc08results.csv

if [ ! -e hwmcc08results.csv ] ; then
  echo Downloading HWMCC08 result table
  wget -q https://fmv.jku.at/hwmcc08/hwmcc08results.csv
fi

echo Running ebmc on the HWMCC08 benchmarks

(# ignore first three lines of hwmcc08results.csv
read -r line
read -r line
read -r line
# now process the lines
while read -r line; do
  BENCHMARK=` echo "$line" | cut -d ',' -f 1 | tr -d '"'`
  if [ ! -e "hwmcc08public-smv/${BENCHMARK}.smv" ] ; then
    echo benchmark $BENCHMARK not found
  else
    RESULT=` echo "$line" | cut -d ',' -f 3 | tr -d '"'`
    if [ "$RESULT" = "uns" ] ; then
      ebmc --bound 2 "hwmcc08public-smv/${BENCHMARK}.smv" > ebmc.out
      if [ $? = 10 ] ; then
        echo $BENCHMARK: got unexpected counterexample
        exit 1
      else
        echo $BENCHMARK: ok "(UNSAT)"
      fi
    fi
    if [ "$RESULT" = "sat" ] ; then
      LENGTH=` echo "$line" | cut -d ',' -f 2`
      if [ "$LENGTH" = "\"*\"" ] ; then
        echo $BENCHMARK: no counterexample length
      else
        ebmc --bound $LENGTH "hwmcc08public-smv/${BENCHMARK}.smv" > ebmc.out
        if [ $? = 10 ] ; then
          echo $BENCHMARK: ok "(SAT $LENGTH)"
        else
          echo $BENCHMARK: failed to find counterexample at bound $LENGTH
          exit 1
        fi
      fi
    fi
  fi
done ) < hwmcc08results.csv
