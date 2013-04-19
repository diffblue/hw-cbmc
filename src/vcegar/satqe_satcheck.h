/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATQE_SATCHECK_H
#define CPROVER_SATQE_SATCHECK_H

#include <solvers/sat/satcheck_zchaff.h>
#include <satqe/sat_cubes.h>

class satqe_satcheckt:public satcheck_zchaff_baset
 {
 public:
  satqe_satcheckt():satcheck_zchaff_baset((solver_ptr=new sat_cubest)) { }
  virtual ~satqe_satcheckt() { delete solver_ptr; }
  
  sat_cubest &solver()
   {
    return *solver_ptr;
   }

  
 protected:
  sat_cubest *solver_ptr;
 };

#endif
