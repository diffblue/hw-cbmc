/*******************************************************************\

Module: Verilog Expression Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_VTYPE_H
#define CPROVER_VERILOG_VTYPE_H

#include <util/type.h>

class vtypet
{
public:
  vtypet():vtype(UNKNOWN)
  {
  }

  explicit vtypet(const typet &src);
  inline unsigned get_width() const { return width; }
  
  inline bool is_bool() const { return vtype==BOOL; }
  inline bool is_signed() const { return vtype==SIGNED; }
  inline bool is_unsigned() const { return vtype==UNSIGNED; }
  inline bool is_integer() const { return vtype==INTEGER; }
  inline bool is_verilog_signed() const { return vtype==VERILOG_SIGNED; }
  inline bool is_verilog_unsigned() const { return vtype==VERILOG_UNSIGNED; }
  inline bool is_verilog_realtime() const { return vtype==VERILOG_REALTIME; }
  inline bool is_other() const { return vtype==OTHER; }

protected:
  typedef enum { UNKNOWN, BOOL, SIGNED, UNSIGNED, INTEGER,
                 VERILOG_SIGNED, VERILOG_UNSIGNED, 
                 VERILOG_REALTIME, OTHER } _vtypet;
  _vtypet vtype;
  unsigned width;
  
  friend std::ostream &operator << (std::ostream &, const vtypet &);
};

std::ostream &operator << (std::ostream &, const vtypet &);

#endif
