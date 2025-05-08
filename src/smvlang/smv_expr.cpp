/*******************************************************************\

Module: SMV Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "smv_expr.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

smv_resize_exprt::smv_resize_exprt(exprt __op, std::size_t __size, typet __type)
  : smv_resize_exprt{
      std::move(__op),
      from_integer(__size, natural_typet{}),
      std::move(__type)}
{
}

smv_extend_exprt::smv_extend_exprt(exprt __op, std::size_t __size, typet __type)
  : smv_extend_exprt{
      std::move(__op),
      from_integer(__size, natural_typet{}),
      std::move(__type)}
{
}
