/*******************************************************************\

Module: BDD Engine

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#if 0
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/property_word_level.h>
#include <trans-word-level/trans_trace_word_level.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/boolbv.h>
#endif

#include "ebmc_base.h"
#include "bdd_engine.h"

/*******************************************************************\

   Class: bdd_enginet

 Purpose:

\*******************************************************************/

class bdd_enginet:public ebmc_baset
{
public:
  bdd_enginet(const cmdlinet &cmdline):ebmc_baset(cmdline)
  {
  }

  int operator()();

protected:
  BDD 
};

/*******************************************************************\

Function: do_bdd

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_bdd(const cmdlinet &cmdline)
{
  return bdd_enginet(cmdline)();
}

/*******************************************************************\

Function: bdd_enginet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int bdd_enginet::operator()()
{
  int result=get_model();
  if(result!=-1) return result;

  if(properties.empty())
  {
    error() << "no properties" << eom;
    return 1;
  }
  
  status() << "Building BDD for transition system" << eom;

  return 0;
}

