/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <parseoptions.h>

class vcegar_parseoptionst:public parseoptions_baset
{
public:
  virtual int doit();
  virtual void help();

  vcegar_parseoptionst(int argc, const char **argv):
    parseoptions_baset(
      "(bmc)(showcubes)(noconstrain)"
      "(nowpcons)(refine1)(nocache)(siege)"
      "(bound):(showparse)(p):(partition): (abstraction):"
      "(showvarmap)(dimacs)(no-simplify)(module):(i):"
      "(showtrans)(init-pred):(discover):"
      "(verbose)(xml-ui)(showcontext)(v):(gcr)"
      "(one_cex_only)(debug)(pred):(more-stats)(relate-init)"
      "(gcrsize):(noinit)(mapping)(modelchecker):(ltl)"
      "(show-modules)(show-claims)(claim):(num-threads):(absref3)",
      argc, argv)
  {
  }
   
  virtual ~vcegar_parseoptionst() { }
};
