/*******************************************************************\

Module: SMV Typechecking

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_SMV_RANGE_H
#define CPROVER_SMV_RANGE_H

#include <util/arith_tools.h>

#include <iosfwd>

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

  typet to_type() const
  {
    return range_typet{from, to};
  }

  static smv_ranget from_type(const range_typet &src)
  {
    return {src.get_from(), src.get_to()};
  }

  bool is_bool() const
  {
    return from == 0 && to == 1;
  }

  bool is_singleton() const
  {
    return from == to;
  }

  smv_ranget operator+(const smv_ranget &other) const
  {
    return {from + other.from, to + other.to};
  }

  smv_ranget operator-(const smv_ranget &other) const
  {
    return {from - other.from, to - other.to};
  }

  smv_ranget operator*(const smv_ranget &other) const
  {
    mp_integer p1 = from * other.from;
    mp_integer p2 = from * other.to;
    mp_integer p3 = to * other.from;
    mp_integer p4 = to * other.to;

    mp_integer from = std::min(p1, std::min(p2, std::min(p3, p4)));
    mp_integer to = std::max(p1, std::max(p2, std::max(p3, p4)));

    return {std::move(from), std::move(to)};
  }

  friend std::ostream &operator<<(std::ostream &, const smv_ranget &);
};

#endif // CPROVER_SMV_RANGE_H
