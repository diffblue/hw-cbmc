/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>
#include <cstdlib>
#include <sstream>

#include <util/ebmc_util.h>
#include <util/lispexpr.h>
#include <util/lispirep.h>
#include <util/std_expr.h>

#include "expr2verilog.h"
#include "expr2verilog_class.h"
#include "verilog_expr.h"
#include "verilog_types.h"

// Precedences (higher means binds more strongly):
// 
// 18  [ ]  bit-select  ( )  parenthesis  ::   .
// 17  unary !  ~  &  |  ~&  ~|  ^  ~^  ^~  +  -
// 16  **  power
// 15  *  /  %
// 14  + -
// 13  <<  >>  <<<  >>>
// 12  >  >=  <  <=
// 11  ==  !=  ===  !==  ==?  !=?
// 10  & 
//  9  ^  ~^  ^~ (binary)
//  8  |
//  7  &&
//  6  ||
//  5  ?:
//  4  ->
//  3  = += -= etc.
//  2  { } concatenation
//  1  {{ }} replication
//  0  SVA stuff

/*******************************************************************\

Function: expr2verilogt::convert_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_if(const if_exprt &src, unsigned precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  std::string dest;
  unsigned p0, p1, p2;

  std::string op0=convert(src.op0(), p0);
  std::string op1=convert(src.op1(), p1);
  std::string op2=convert(src.op2(), p2);

  if(precedence>p0) dest+='(';
  dest+=op0;
  if(precedence>p0) dest+=')';

  dest+=" ? ";

  if(precedence>p1) dest+='(';
  dest+=op1;
  if(precedence>p1) dest+=')';

  dest+=" : ";

  if(precedence>p2) dest+='(';
  dest+=op2;
  if(precedence>p2) dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_cycle_delay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_sva_cycle_delay(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  std::string dest="##";
  
  unsigned p2;

  std::string op0=convert(src.op0());
  std::string op1=convert(src.op1());
  std::string op2=convert(src.op2(), p2);

  if(src.op1().is_nil())
    dest+=op0;
  else if(src.op1().id()==ID_infinity)
    dest+='['+op0+':'+'$'+']';
  else
    dest+='['+op0+':'+op1+']';
    
  dest+=' ';

  if(precedence>p2) dest+='(';
  dest+=op2;
  if(precedence>p2) dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_sequence_concatenation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_sva_sequence_concatenation(
  const binary_exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  std::string dest;

  unsigned p0, p1;  
  std::string op0=convert(src.op0(), p0);
  std::string op1=convert(src.op1(), p1);

  if(precedence>p0) dest+='(';
  dest+=op0;
  if(precedence>p0) dest+=')';

  dest+=' ';

  if(precedence>p1) dest+='(';
  dest+=op1;
  if(precedence>p1) dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_binary(
  const multi_ary_exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  if(src.operands().size()<2)
    return convert_norep(src, precedence);

  bool first=true;
  std::string dest;

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
    {
      dest+=' ';
      dest+=symbol;
      dest+=' ';
    }

    unsigned p;
    std::string op=convert(*it, p);

    if(precedence>p) dest+='(';
    dest+=op;
    if(precedence>p) dest+=')';
  }

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string
expr2verilogt::convert_with(const with_exprt &src, unsigned precedence)
{
  if(src.operands().size()<1)
    return convert_norep(src, precedence);

  unsigned p;
  std::string dest = "(" + convert(src.old(), p);

  for(unsigned i=1; i<src.operands().size(); i+=2)
  {
    dest+=" WITH ";
    dest+=convert(src.operands()[i], p);
    dest+=":=";
    dest+=convert(src.operands()[i+1], p);
  }

  dest+=")";

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_concatenation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_concatenation(
  const concatenation_exprt &src,
  unsigned precedence)
{
  if(src.operands().size()<1)
    return convert_norep(src, precedence);

  bool first=true;
  std::string dest="{ ";

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
      dest+=", ";

    unsigned p;
    std::string op=convert(*it, p);

    if(precedence>p) dest+='(';
    dest+=op;
    if(precedence>p) dest+=')';
  }

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_function(
  const std::string &name,
  const exprt &src)
{
  bool first=true;
  std::string dest=name;
  dest+="(";

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
      dest+=", ";

    unsigned p;
    std::string op=convert(*it, p);
    dest+=op;
  }

  dest+=")";

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_function_call(const function_call_exprt &src)
{
  if(src.operands().size()!=2)
  {
    unsigned p;
    return convert_norep(src, p);
  }

  unsigned p;  
  std::string fkt=convert(src.op0(), p);

  std::string dest=fkt;
  bool first=true;
  dest+="(";

  for(const auto & op : src.op1().operands())
  {
    if(first)
      first=false;
    else
      dest+=", ";

    unsigned p;
    dest+=convert(op, p);
  }

  dest+=")";

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_sva

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_sva(
  const std::string &name,
  const exprt &src)
{
  if(src.operands().size()==1)
    return name + " " + convert(to_unary_expr(src).op());
  else if(src.operands().size()==2)
  {
    auto &binary_expr = to_binary_expr(src);
    return convert(binary_expr.op0()) + " " + name + " " +
           convert(binary_expr.op1());
  }
  else
    return "?";
}

/*******************************************************************\

Function: expr2verilogt::convert_replication

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_replication(
  const replication_exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  std::string dest="{ ";

  dest+=convert(src.op0());
  dest+=" { ";
  dest+=convert(src.op1());
  dest+=" } }";

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_unary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_unary(
  const unary_exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);
    
  unsigned p;
  std::string op = convert(src.op(), p);

  std::string dest=symbol;
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_typecast(
  const typecast_exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()==1)
  {
    //const typet &from=src.op0().type();
    //const typet &to=src.type();

    // just ignore them for now
    return convert(src.op(), precedence);
  }

  return convert_norep(src, precedence);
}

/*******************************************************************\

Function: expr2verilogt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_index(
  const index_exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op=convert(src.op0(), p);

  std::string dest;
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  dest+='[';
  dest+=convert(src.op1());
  dest+=']';

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_extractbit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_extractbit(
  const extractbit_exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op=convert(src.op0(), p);

  std::string dest;
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  dest+='[';
  dest+=convert(src.op1());
  dest+=']';

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_extractbits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_extractbits(
  const extractbits_exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op = convert(src.src(), p);

  std::string dest;
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  dest+='[';
  dest += convert(src.upper());
  dest+=':';
  dest += convert(src.lower());
  dest+=']';

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string
expr2verilogt::convert_member(const member_exprt &src, unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op = convert(src.compound(), p);

  std::string dest;
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  dest+='.';
  dest += id2string(src.get_component_name());

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_norep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_norep(
  const exprt &src,
  unsigned &precedence)
{
  precedence=22;
  return src.pretty();
}

/*******************************************************************\

Function: expr2verilogt::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_symbol(
  const exprt &src,
  unsigned &precedence)
{
  precedence=22;
  std::string dest=src.get_string(ID_identifier);
 
  if(std::string(dest, 0, 9)=="Verilog::")
    dest.erase(0, 9);

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_nondet_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_nondet_symbol(
  const exprt &src,
  unsigned &precedence)
{
  return "nondet("+convert_symbol(src, precedence)+")";
}

/*******************************************************************\

Function: expr2verilogt::convert_next_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_next_symbol(
  const exprt &src,
  unsigned &precedence)
{
  return "next("+convert_symbol(src, precedence)+")";
}

/*******************************************************************\

Function: expr2verilogt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_constant(
  const constant_exprt &src,
  unsigned &precedence)
{
  precedence=22;

  const typet &type=src.type();
  const irep_idt &value=src.get_value();
  std::string dest;

  if(type.id()==ID_bool)
  {
    if(src.is_true())
      dest+='1';
    else
      dest+='0';
  }
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv)
  {
    unsigned width=to_bitvector_type(type).get_width();
  
    mp_integer i;
    to_integer_non_constant(binary_to_hex(src), i);

    if(i>=256)
      dest="'h"+integer2string(i, 16);
    else if(width<=7)
    {
      dest=std::to_string(width);
      dest+="'";
      if(type.id()==ID_signedbv) dest+='s';
      dest+='b';
      dest+=integer2string(i, 2);
    }
    else
      dest=integer2string(i);
  }
  else if(type.id()==ID_verilog_signedbv)
  {
    unsigned width=to_verilog_signedbv_type(src.type()).get_width();
    return std::to_string(width)+"'sb"+id2string(value);
  }
  else if(type.id()==ID_verilog_unsignedbv)
  {
    unsigned width=to_verilog_unsignedbv_type(src.type()).get_width();
    return std::to_string(width)+"'b"+id2string(value);
  }
  else if(type.id()==ID_integer || type.id()==ID_natural ||
          type.id()==ID_range)
    dest=id2string(value);
  else
    return convert_norep(src, precedence);

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert_array(
  const exprt &src,
  unsigned precedence)
{
  std::string dest="{ ";

  forall_operands(it, src)
  {
    std::string tmp=convert(*it, precedence);
      
    exprt::operandst::const_iterator next_it=it;
    next_it++;

    if(next_it!=src.operands().end())
    {
      tmp+=", ";
      if(tmp.size()>40) tmp+="\n    ";
    }

    dest+=tmp;
  }

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2verilogt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert(
  const exprt &src,
  unsigned &precedence)
{
  precedence=20; // max

  if(src.id()==ID_plus)
    return convert_binary(to_multi_ary_expr(src), "+", precedence = 14);

  else if(src.id()==ID_if)
    return convert_if(to_if_expr(src), precedence=5);

  else if(src.id()==ID_concatenation)
    return convert_concatenation(to_concatenation_expr(src), precedence=2);

  else if(src.id()==ID_with)
    return convert_with(to_with_expr(src), precedence);

  else if(src.id()==ID_replication)
    return convert_replication(to_replication_expr(src), precedence=1);

  else if(src.id()==ID_array)
    return convert_array(src, precedence);

  else if(src.id()==ID_minus)
  {
    if(src.operands().size()!=2)
      return convert_norep(src, precedence);
    else
      return convert_binary(to_multi_ary_expr(src), "-", precedence = 14);
  }

  else if(src.id()==ID_shl)
    return convert_binary(to_multi_ary_expr(src), "<<", precedence = 13);

  else if(src.id()==ID_lshr)
    return convert_binary(to_multi_ary_expr(src), ">>", precedence = 13);

  else if(src.id()==ID_ashr)
    return convert_binary(to_multi_ary_expr(src), ">>>", precedence = 13);

  else if(src.id()==ID_unary_minus)
    return convert_unary(to_unary_minus_expr(src), "-", precedence = 17);

  else if(src.id()==ID_unary_plus)
    return convert_unary(to_unary_plus_expr(src), "+", precedence = 17);

  else if(src.id()==ID_index)
    return convert_index(to_index_expr(src), precedence=18);

  else if(src.id()==ID_extractbit)
    return convert_extractbit(to_extractbit_expr(src), precedence=18);

  else if(src.id()==ID_extractbits)
    return convert_extractbits(to_extractbits_expr(src), precedence=18);

  else if(src.id()==ID_member)
    return convert_member(to_member_expr(src), precedence=18);

  else if(src.id()==ID_mult)
    return convert_binary(to_multi_ary_expr(src), "*", precedence = 15);

  else if(src.id()==ID_div)
    return convert_binary(to_multi_ary_expr(src), "/", precedence = 15);

  else if(src.id()==ID_lt)
    return convert_binary(to_multi_ary_expr(src), "<", precedence = 12);

  else if(src.id()==ID_gt)
    return convert_binary(to_multi_ary_expr(src), ">", precedence = 12);

  else if(src.id()==ID_le)
    return convert_binary(to_multi_ary_expr(src), "<=", precedence = 12);

  else if(src.id()==ID_ge)
    return convert_binary(to_multi_ary_expr(src), ">=", precedence = 12);

  else if(src.id()==ID_equal)
    return convert_binary(to_multi_ary_expr(src), "==", precedence = 11);

  else if(src.id()==ID_notequal)
    return convert_binary(to_multi_ary_expr(src), "!=", precedence = 11);

  else if(src.id()==ID_verilog_case_equality)
    return convert_binary(to_multi_ary_expr(src), "===", precedence = 11);

  else if(src.id()==ID_verilog_case_inequality)
    return convert_binary(to_multi_ary_expr(src), "!==", precedence = 11);

  else if(src.id()==ID_not)
    return convert_unary(to_not_expr(src), "!", precedence = 17);

  else if(src.id()==ID_bitnot)
    return convert_unary(to_bitnot_expr(src), "~", precedence = 17);

  else if(src.id()==ID_typecast)
    return convert_typecast(to_typecast_expr(src), precedence);

  else if(src.id()==ID_and)
    return convert_binary(to_multi_ary_expr(src), "&&", precedence = 7);

  else if(src.id()==ID_power)
    return convert_binary(to_multi_ary_expr(src), "**", precedence = 16);

  else if(src.id()==ID_bitand)
    return convert_binary(to_multi_ary_expr(src), "&", precedence = 10);

  else if(src.id()==ID_bitxor)
    return convert_binary(to_multi_ary_expr(src), "^", precedence = 9);

  else if(src.id()==ID_bitxnor)
    return convert_binary(to_multi_ary_expr(src), "~^", precedence = 9);

  else if(src.id()==ID_mod)
    return convert_binary(to_multi_ary_expr(src), "%", precedence = 15);

  else if(src.id()==ID_or)
    return convert_binary(to_multi_ary_expr(src), "||", precedence = 6);

  else if(src.id()==ID_bitor)
    return convert_binary(to_multi_ary_expr(src), "|", precedence = 8);

  else if(src.id()==ID_implies)
    return convert_binary(to_multi_ary_expr(src), "|->", precedence = 0);

  else if(src.id()==ID_iff)
    return convert_binary(to_multi_ary_expr(src), "<->", precedence = 0);

  else if(src.id()==ID_reduction_or)
    return convert_unary(to_unary_expr(src), "|", precedence = 17);

  else if(src.id()==ID_reduction_and)
    return convert_unary(to_unary_expr(src), "&", precedence = 17);

  else if(src.id()==ID_reduction_nor)
    return convert_unary(to_unary_expr(src), "~|", precedence = 17);

  else if(src.id()==ID_reduction_nand)
    return convert_unary(to_unary_expr(src), "~&", precedence = 17);

  else if(src.id()==ID_reduction_xor)
    return convert_unary(to_unary_expr(src), "^", precedence = 17);

  else if(src.id()==ID_reduction_xnor)
    return convert_unary(to_unary_expr(src), "~^", precedence = 17);

  else if(src.id()==ID_AG || src.id()==ID_EG ||
          src.id()==ID_AX || src.id()==ID_EX)
    return convert_unary(
      to_unary_expr(src), src.id_string() + " ", precedence = 0);

  else if(src.id()==ID_symbol)
    return convert_symbol(src, precedence);

  else if(src.id()==ID_nondet_symbol)
    return convert_nondet_symbol(src, precedence);

  else if(src.id()==ID_next_symbol)
    return convert_next_symbol(src, precedence);

  else if(src.id()==ID_constant)
    return convert_constant(to_constant_expr(src), precedence);
    
  else if(src.id()==ID_constraint_select_one)
    return convert_function("$ND", src);
    
  else if(src.id()==ID_onehot)
    return convert_function("$onehot", src);
    
  else if(src.id()==ID_onehot0)
    return convert_function("$onehot0", src);

  else if(src.id()==ID_sva_overlapped_implication)
    return convert_binary(to_multi_ary_expr(src), "|->", precedence = 0);
    // not sure about precedence
    
  else if(src.id()==ID_sva_non_overlapped_implication)
    return convert_binary(to_multi_ary_expr(src), "|=>", precedence = 0);
    // not sure about precedence
    
  else if(src.id()==ID_sva_cycle_delay)
    return convert_sva_cycle_delay(src, precedence=0);
    // not sure about precedence
    
  else if(src.id()==ID_sva_sequence_concatenation)
    return convert_sva_sequence_concatenation(
      to_binary_expr(src), precedence = 0);
    // not sure about precedence
    
  else if(src.id()==ID_sva_always)
    return convert_sva("always", src);

  else if(src.id()==ID_sva_nexttime)
    return convert_sva("nexttime", src);

  else if(src.id()==ID_sva_s_nexttime)
    return convert_sva("s_nexttime", src);

  else if(src.id()==ID_sva_eventually)
    return convert_sva("eventually", src);

  else if(src.id()==ID_sva_s_eventually)
    return convert_sva("s_eventually", src);

  else if(src.id()==ID_sva_until)
    return convert_sva("until", src);

  else if(src.id()==ID_sva_s_until)
    return convert_sva("s_until", src);

  else if(src.id()==ID_sva_until_with)
    return convert_sva("until_with", src);

  else if(src.id()==ID_sva_s_until_with)
    return convert_sva("s_until_with", src);
    
  else if(src.id()==ID_function_call)
    return convert_function_call(to_function_call_expr(src));

  // no VERILOG language expression for internal representation 
  return convert_norep(src, precedence);
}

/*******************************************************************\

Function: expr2verilogt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert(const exprt &src)
{
  unsigned precedence;
  return convert(src, precedence);
}

/*******************************************************************\

Function: expr2verilogt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert(const typet &type)
{
  if(type.id()==ID_bool)
    return "bool";
  else if(type.id()==ID_unsignedbv || type.id()==ID_signedbv)
  {
    unsigned width=to_bitvector_type(type).get_width();
    bool little_endian=type.get_bool(ID_C_little_endian);
    unsigned offset=atoi(type.get(ID_C_offset).c_str());

    if(width!=0)
    {
      std::string dest;
      if(type.id()==ID_unsignedbv)
        dest="";
      else if(type.id()==ID_signedbv)
        dest="signed ";

      dest+='[';
      
      if(little_endian)
      {
        dest+=std::to_string(offset+width-1);
        dest+=":";
        dest+=std::to_string(offset);
      }
      else
      {
        dest+=std::to_string(offset);
        dest+=":";
        dest+=std::to_string(offset+width-1);
      }

      dest+="]";
      return dest;
    }
  }
  else if(type.id()==ID_array)
  {
    auto &array_type = to_array_type(type);
    std::string dest="array [";

    dest += convert(array_type.size());

    dest+="] of ";
    dest += convert(array_type.subtype());

    return dest;
  }
  else if(type.id()==ID_genvar)
    return "genvar";
  else if(type.id()==ID_integer)
    return "integer";
  else if(type.id()==ID_real || type.id()==ID_verilog_realtime)
    return "real";

  return "IREP("+type.pretty()+")";
}

/*******************************************************************\

Function: expr2verilog

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilog(const exprt &expr)
{
  expr2verilogt expr2verilog;
  return expr2verilog.convert(expr);
}

/*******************************************************************\

Function: type2verilog

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type2verilog(const typet &type)
{
  expr2verilogt expr2verilog;
  return expr2verilog.convert(type);
}
