/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bmc.h"
#include "parseoptions.h"
#include "vcegar.h"

/*******************************************************************\

Function: vcegar_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int vcegar_parseoptionst::doit()
{
  if(cmdline.isset("bmc") ||
     cmdline.isset("show-claims") ||
     cmdline.isset("show-modules"))
  {
    bmct bmc(cmdline);
  
    int result=bmc.get_model();
    if(result!=-1) return result;

    return bmc.do_sat();
  }
  
  // do CEGAR
  return do_vcegar(cmdline);
}

/*******************************************************************\

Function: vcegar_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void vcegar_parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *             VCEGAR Copyright 1.3 (C) 2003-2007          * *\n"
    "* * Carnegie Mellon University, Computer Science Department * *\n"
    "* *         ETH Zuerich, Computer Systems Institute         * *\n"
    "* *                   hjain@cs.cmu.edu                      * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                          Purpose:\n"
    "\n"
    " vcegar [-?] [-h] [--help]      show help\n"
    " vcegar file ...                source file name\n"
    "\n"
    "General options:\n"
    " vcegar --p <propfile>          specify property in a file\n"
    " vcegar --module <module>       set module (default: main)\n"
    " vcegar --claim <nr>            Specify property number from the model file (similar to Cadence SMV)\n"
    " vcegar --partition <nr>        Strategy for partitioning the predicates \n" 
    "    nr = 2                      All related (by weakest preconditions) next state and current\n"
    "                                state predicates together. (Not very scalable) \n"
    "    nr = 6                      Only next state predicates with exactly same symbols kept together (default)\n"
    "    nr = 8                      Initial abstraction is simply true (completely lazy)\n"
    "\n"
    "Less frequently used options:\n"
    " vcegar --i <nr>                Limit the number of iterations in the CEGAR loop to <nr>\n"
    " vcegar --pred <file>           Use predicates from the given file  \n"
    " vcegar --mapping               Write predicate to boolean variable mapping in vcegar.map\n"
    " vcegar --modelchecker <num>    Which modelchecker to use for checking abstractions\n"
    "   num=nusmv                    Use NuSMV binary named NuSMV  \n"
    "   num=cadencesmv               Use Cadence SMV binary named smv (default)\n"
    " vcegar --absref3               Give this option to Cadence SMV              \n"
    " vcegar --gcr                   Generates clusters from refinement of spurious transitions. \n"  
    " vcegar --gcrsize <nr>          Maximum cluster size when generating clusters from refinement  \n"
    " vcegar --noinit                Do not compute initial set of abstract states\n"
 
   "\n"
    "Even less frequently used (use at your own risk):\n"
    "---------------------\n"

    " vcegar --discover <nr>         How to extract predicates from weakest preconditions etc. \n" 
    "    nr = 1                      takes guards and boolean expressions involving case as predicates\n"  
    "    nr = 2                      only simple expressions allowed in predicates (default)\n"  
    " vcegar --noconstrain           Refine using new predicates only. \n"  
    "                                Don't constrain using abstract spurious transitions.\n"
    " vcegar --init-pred <nr>        Choice of initial set of predicates \n"
    "    nr = 1                      property itself is taken as initial predicate \n"
    "    nr = 2                      initial predicates are extracted from property (default)\n"   
    " vcegar --showcubes             Shows the cubes generated for each cluster\n"  
    " vcegar --one_cex_only          Remove only one spurious abstract transition\n"  
    "                                And not as much as possible using unsat cores\n"

    " vcegar --more-stats            Prints runtime statistics after each iteration\n"
    " vcegar --relate-init           Find constrains between current state predicates having same symbols\n"
    " vcegar --discover <nr>         Predicate discovery technique (default=2)\n"
    " vcegar --nowpcons              Do not add weakest pre-condition constraints\n"
    " vcegar --nocache               Do not cache already computed abstractions\n"
    " vcegar --no-simplify           disable simplificaton\n"
    "\n"
    "Bounded Model checking:\n"
    "----------------------\n"
    " vcegar --bmc                   For bounded model checking (default: predicate abstraction)\n"
    " vcegar --bound <nr>            Set bound for BMC\n"
    " vcegar --dimacs                Output CNF in Dimacs CNF format\n"
    "\n"
    "Debugging options:\n"
    " vcegar --showparse           show parse trees\n"
    " vcegar --showvarmap          show variable map\n"
    " vcegar --showcontext         show the context\n"
    " vcegar --showtrans           show the three components of the transition relation\n"
    "\n";
}
