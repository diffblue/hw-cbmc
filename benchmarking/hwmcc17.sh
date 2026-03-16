#!/bin/sh

# ca. 30 minutes

if [ ! -e aiger/. ] ; then
  echo Downloading and building the AIGER tools
  git clone https://github.com/arminbiere/aiger
  (cd aiger ; ./configure.sh ; make aigtosmv )
fi

if [ ! -e hwmcc17-single/. ] ; then
  echo Downloading HWMCC17 benchmark archive
  wget -q https://fmv.jku.at/hwmcc17/hwmcc17-single-benchmarks.tar.xz
  xz -d hwmcc17-single-benchmarks.tar.xz
  mkdir hwmcc17-single
  (cd hwmcc17-single ; tar xf ../hwmcc17-single-benchmarks.tar)
  rm hwmcc17-single-benchmarks.tar
fi

if [ ! -e hwmcc17-single-smv/. ] ; then
  echo Converting AIGER to SMV
  mkdir hwmcc17-single-smv
  (cd hwmcc17-single; for FILE in *.aig ; do
    SMV=`echo "$FILE" | sed s/.aig/.smv/`
    ../aiger/aigtosmv -b "$FILE" "../hwmcc17-single-smv/$SMV"
  done)
fi

# expected answers from the abcdeep result column

if [ ! -e hwmcc17-single.csv ] ; then
  echo Downloading HWMCC17 result table
  wget -q https://fmv.jku.at/hwmcc17/single.csv -O hwmcc17-single.csv
fi

echo Running ebmc on the HWMCC17 benchmarks

(# ignore the first line of single.csv
read -r line
# now process the lines
while read -r line; do
  BENCHMARK=` echo "$line" | cut -d ';' -f 1 `
  if [ "$BENCHMARK" = "6s218b2950" ] ||
     [ "$BENCHMARK" = "6s221rb14" ] ||
     [ "$BENCHMARK" = "6s299b685" ] ||
     [ "$BENCHMARK" = "6s374b029" ] ||
     [ "$BENCHMARK" = "oski15a01b57s" ] ||
     [ "$BENCHMARK" = "6s374b114" ] ||
     [ "$BENCHMARK" = "oski15a08b08s" ] ; then
    # skip, SMV file too large for Bison stack
    echo $BENCHMARK: skipping
    continue
  fi
  if [ "$BENCHMARK" = "6s320rb1" ] ||
     [ "$BENCHMARK" = "intel036" ] ; then
    # skip, too slow
    echo $BENCHMARK: skipping
    continue
  fi
  if [ ! -e "hwmcc17-single-smv/${BENCHMARK}.smv" ] ; then
    echo benchmark $BENCHMARK not found
  else
    RESULT=` echo "$line" | cut -d ';' -f 3 `
    if [ "$RESULT" = "uns" ] ; then
      ebmc --bound 2 "hwmcc17-single-smv/${BENCHMARK}.smv" > ebmc.out
      if [ $? = 10 ] ; then
        echo $BENCHMARK: got unexpected couterexample
        exit 1
      else
        echo $BENCHMARK: ok "(UNSAT)"
      fi
    fi
    if [ "$RESULT" = "sat" ] ; then
      LENGTH=` echo "$line" | cut -d ';' -f 4`
      if [ "$LENGTH" = "\"*\"" ] ; then 
        echo $BENCHMARK: no counterexample length
      else
        ebmc --bound $LENGTH "hwmcc17-single-smv/${BENCHMARK}.smv" > ebmc.out
        if [ $? = 10 ] ; then
          echo $BENCHMARK: ok "(SAT $LENGTH)"
        else
          echo $BENCHMARK: failed to find couterexample at bound $LENGTH
          exit 1
        fi
      fi
    fi
  fi
done ) < hwmcc17-single.csv
