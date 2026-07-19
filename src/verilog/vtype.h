/*******************************************************************\

Module: Verilog Expression Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_VTYPE_H
#define CPROVER_VERILOG_VTYPE_H

#include <util/type.h>

/// a Verilog non-composite type, including
/// integral types (1800 2017 6.11.1), realtime types,
/// string
class vtypet
{
public:
  vtypet():vtype(UNKNOWN)
  {
  }

  explicit vtypet(const typet &src);
  inline unsigned get_width() const { return width; }
  
  inline bool is_bool() const { return vtype==BOOL; }
  inline bool is_signed_bit() const
  {
    return vtype == SIGNED_BIT;
  }
  inline bool is_unsigned_bit() const
  {
    return vtype == UNSIGNED_BIT;
  }
  inline bool is_integer() const { return vtype==INTEGER; }
  inline bool is_signed_logic() const
  {
    return vtype == SIGNED_LOGIC;
  }
  inline bool is_unsigned_logic() const
  {
    return vtype == UNSIGNED_LOGIC;
  }
  inline bool is_real() const
  {
    return vtype == REAL;
  }
  bool is_null() const
  {
    return vtype == NULL_TYPE;
  }
  bool is_chandle() const
  {
    return vtype == CHANDLE;
  }
  inline bool is_event() const
  {
    return vtype == EVENT;
  }
  bool is_string() const
  {
    return vtype == STRING;
  }
  inline bool is_other() const { return vtype==OTHER; }

  bool is_signed_integral() const
  {
    return vtype == SIGNED_BIT || vtype == SIGNED_LOGIC;
  }

  bool is_unsigned_integral() const
  {
    return vtype == BOOL || vtype == UNSIGNED_BIT || vtype == UNSIGNED_LOGIC;
  }

  bool is_two_valued() const
  {
    return vtype == BOOL || vtype == SIGNED_BIT || vtype == UNSIGNED_BIT;
  }

  bool is_four_valued() const
  {
    return vtype == SIGNED_LOGIC || vtype == UNSIGNED_LOGIC;
  }

protected:
  typedef enum
  {
    UNKNOWN,
    BOOL,
    SIGNED_BIT,
    UNSIGNED_BIT,
    INTEGER,
    SIGNED_LOGIC,
    UNSIGNED_LOGIC,
    REAL,
    NULL_TYPE,
    CHANDLE,
    EVENT,
    STRING,
    OTHER
  } _vtypet;
  _vtypet vtype;
  unsigned width;
  
  friend std::ostream &operator << (std::ostream &, const vtypet &);
};

std::ostream &operator << (std::ostream &, const vtypet &);

#endif
