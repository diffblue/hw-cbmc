/*******************************************************************\

Module: AIG Substitution Map

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// AIG Substitution Map

#ifndef CPROVER_TRANS_NETLIST_AIG_SUBSTITUTION_H
#define CPROVER_TRANS_NETLIST_AIG_SUBSTITUTION_H

#include <solvers/prop/literal.h>

#include <vector>

/// Maps old AIG variable numbers to new literals.
class aig_substitution_mapt
{
public:
  explicit aig_substitution_mapt(std::size_t size) : map(size)
  {
    // default identity mapping
    for(std::size_t i = 0; i < size; i++)
      map[i] = literalt{narrow_cast<literalt::var_not>(i), false};
  }

  /// Apply the substitution to a literal.
  literalt operator()(literalt l) const
  {
    if(l.is_constant())
      return l;
    else
    {
      PRECONDITION(l.var_no() < size());
      return map[l.var_no()] ^ l.sign();
    }
  }

  std::size_t size() const
  {
    return map.size();
  }

  literalt &operator[](literalt::var_not var_no)
  {
    return map[var_no];
  }

  const literalt &operator[](literalt::var_not var_no) const
  {
    return map[var_no];
  }

private:
  std::vector<literalt> map;
};

#endif // CPROVER_TRANS_NETLIST_AIG_SUBSTITUTION_H
