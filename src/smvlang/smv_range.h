/*******************************************************************\

Module: SMV Typechecking

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_SMV_RANGE_H
#define CPROVER_SMV_RANGE_H

#include <util/arith_tools.h>

class smv_ranget
{
public:
  smv_ranget() : from(0), to(0)
  {
  }

  smv_ranget(mp_integer _from, mp_integer _to)
    : from(std::move(_from)), to(std::move(_to))
  {
    PRECONDITION(_from <= _to);
  }

  mp_integer from, to;

  bool is_contained_in(const smv_ranget &other) const
  {
    if(other.from > from)
      return false;
    if(other.to < to)
      return false;
    return true;
  }

  void make_union(const smv_ranget &other)
  {
    mp_min(from, other.from);
    mp_max(to, other.to);
  }

  void to_type(typet &dest) const
  {
    dest = typet(ID_range);
    dest.set(ID_from, integer2string(from));
    dest.set(ID_to, integer2string(to));
  }

  bool is_bool() const
  {
    return from == 0 && to == 1;
  }

  bool is_singleton() const
  {
    return from == to;
  }

  smv_ranget &operator+(const smv_ranget &other)
  {
    from += other.from;
    to += other.to;
    return *this;
  }

  smv_ranget &operator-(const smv_ranget &other)
  {
    from -= other.from;
    to -= other.to;
    return *this;
  }

  smv_ranget &operator*(const smv_ranget &other)
  {
    mp_integer p1 = from * other.from;
    mp_integer p2 = from * other.to;
    mp_integer p3 = to * other.from;
    mp_integer p4 = to * other.to;

    from = std::min(p1, std::min(p2, std::min(p3, p4)));
    to = std::max(p1, std::max(p2, std::max(p3, p4)));

    return *this;
  }
};

#endif // CPROVER_SMV_RANGE_H
