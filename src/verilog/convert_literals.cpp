/*******************************************************************\

Module: Conversion for Verilog Literals

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "convert_literals.h"

#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/string2int.h>

#include <ebmc/ebmc_error.h>

#include "verilog_types.h"

constant_exprt convert_string_literal(const irep_idt &value)
{
  // These are unsigned integer vectors with 8 bits per character.
  // The first character is the most significant one.
  auto type = unsignedbv_typet{value.size() * 8};

  // The below is quadratic, and should be made linear.
  mp_integer new_value = 0;
  for(std::size_t i = 0; i < value.size(); i++)
  {
    unsigned char character = value[i];
    new_value += mp_integer(character) << ((value.size() - i - 1) * 8);
  }

  return from_integer(new_value, type);
}

constant_exprt convert_real_literal(const irep_idt &value)
{
  // first, get rid of whitespace and underscores
  // and make everything lower case
  std::string rest;
  rest.reserve(value.size());

  for(unsigned i = 0; i < value.size(); i++)
  {
    char ch = value[i];
    if(!isspace(ch) && ch != '_')
      rest += tolower(ch);
  }

  const char *p = rest.c_str();

  std::string str_whole_number, str_fraction_part, str_exponent;

  // get whole number part
  while(*p != '.' && *p != 0 && *p != 'e')
  {
    str_whole_number += *p;
    p++;
  }

  // skip dot
  if(*p == '.')
    p++;

  // get fraction part
  while(*p != 0 && *p != 'e')
  {
    str_fraction_part += *p;
    p++;
  }

  // skip e
  if(*p == 'e')
    p++;

  // skip +
  if(*p == '+')
    p++;

  // get exponent
  while(*p != 0)
  {
    str_exponent += *p;
    p++;
  }

  std::string str_number = str_whole_number + str_fraction_part;

  mp_integer significand;

  if(str_number.empty())
    significand = 0;
  else
    significand = string2integer(str_number, 10);

  mp_integer exponent;

  if(str_exponent.empty())
    exponent = 0;
  else
    exponent = string2integer(str_exponent, 10);

  // adjust exponent
  exponent -= str_fraction_part.size();

  // IEEE 1800-2017 5.7.2 says that real literal constants
  // are IEEE 754 double-precision, but doesn't specify
  // how to round when converting decimals.
  ieee_floatt ieee_float{
    ieee_float_spect::double_precision(),
    ieee_floatt::rounding_modet::ROUND_TO_EVEN};

  ieee_float.from_base10(significand, exponent);

  constant_exprt result = ieee_float.to_expr();
  result.type() = verilog_real_typet{};

  return result;
}

constant_exprt convert_integral_literal(const irep_idt &value)
{
  // first, get rid of whitespace and underscores
  // and make everything lower case
  std::string rest;
  rest.reserve(value.size());

  for(unsigned i = 0; i < value.size(); i++)
  {
    char ch = value[i];
    if(!isspace(ch) && ch != '_')
      rest += tolower(ch);
  }

  // special case the "unbased unsized literals"
  if(rest == "'0")
  {
    return from_integer(0, unsignedbv_typet{1});
  }
  else if(rest == "'1")
  {
    return from_integer(1, unsignedbv_typet{1});
  }
  else if(rest == "'x" || rest == "'X")
  {
    return constant_exprt{"x", verilog_unsignedbv_typet{1}};
  }
  else if(rest == "'z" || rest == "'Z")
  {
    return constant_exprt{"z", verilog_unsignedbv_typet{1}};
  }

  std::string::size_type pos = rest.find('\'');
  std::size_t bits = 0;
  bool bits_given = false;

  if(pos != std::string::npos) // size given?
  {
    if(rest[0] != '\'')
    {
      bits = safe_string2size_t(rest);
      bits_given = true;
    }

    rest = rest.substr(pos + 1);
  }

  // signed-flag 's' used?
  bool s_flag_given = false;

  if(rest != "" && tolower(rest[0]) == 's')
  {
    s_flag_given = true;
    rest = rest.substr(1);
  }

  // special case for 'dx/'dX/'dz/'dZ
  // "The default length of x and z is the same as the default length of an integer."
  // Introduced by Verilog 1364-2001.
  if(rest == "dx" || rest == "dX")
  {
    std::size_t final_bits = bits_given ? bits : 32;
    auto type = s_flag_given
                  ? static_cast<typet>(verilog_signedbv_typet{final_bits})
                  : verilog_unsignedbv_typet{final_bits};
    return constant_exprt{std::string(final_bits, 'x'), type};
  }
  else if(rest == "dz" || rest == "dZ")
  {
    std::size_t final_bits = bits_given ? bits : 32;
    auto type = s_flag_given
                  ? static_cast<typet>(verilog_signedbv_typet{final_bits})
                  : verilog_unsignedbv_typet{final_bits};
    return constant_exprt{std::string(final_bits, 'z'), type};
  }

  unsigned base = 10;

  // base given?
  bool based = false;

  if(rest != "")
  {
    switch(rest[0])
    {
    case 'b':
      based = true;
      base = 2;
      rest.erase(0, 1);
      break;
    case 'd':
      based = true;
      base = 10;
      rest.erase(0, 1);
      break;
    case 'h':
      based = true;
      base = 16;
      rest.erase(0, 1);
      break;
    case 'o':
      based = true;
      base = 8;
      rest.erase(0, 1);
      break;
    default:
      base = 10;
    }
  }

  // based numbers are always unsigned unless 's' flag is given
  bool is_signed = !based || s_flag_given;

  // check for z/x
  bool four_valued = false;

  for(unsigned i = 0; i < rest.size(); i++)
    if(rest[i] == '?' || rest[i] == 'z' || rest[i] == 'x')
      four_valued = true;

  if(base != 10)
  {
    // expand bits

    std::string full_value = rest;
    std::string bit_value;

    switch(base)
    {
    case 2:
      bit_value = full_value;
      break;

    case 8:
      for(unsigned i = 0; i < full_value.size(); i++)
      {
        switch(full_value[i])
        {
        // clang-format off
        case '0': bit_value+="000"; break;
        case '1': bit_value+="001"; break;
        case '2': bit_value+="010"; break;
        case '3': bit_value+="011"; break;
        case '4': bit_value+="100"; break;
        case '5': bit_value+="101"; break;
        case '6': bit_value+="110"; break;
        case '7': bit_value+="111"; break;
        case 'x': bit_value+="xxx"; break;
        case 'z': bit_value+="zzz"; break;
          // clang-format on
        }
      }
      break;

    case 16:
      for(unsigned i = 0; i < full_value.size(); i++)
      {
        switch(full_value[i])
        {
        // clang-format off
        case '0': bit_value+="0000"; break;
        case '1': bit_value+="0001"; break;
        case '2': bit_value+="0010"; break;
        case '3': bit_value+="0011"; break;
        case '4': bit_value+="0100"; break;
        case '5': bit_value+="0101"; break;
        case '6': bit_value+="0110"; break;
        case '7': bit_value+="0111"; break;
        case '8': bit_value+="1000"; break;
        case '9': bit_value+="1001"; break;
        case 'a': bit_value+="1010"; break;
        case 'b': bit_value+="1011"; break;
        case 'c': bit_value+="1100"; break;
        case 'd': bit_value+="1101"; break;
        case 'e': bit_value+="1110"; break;
        case 'f': bit_value+="1111"; break;
        case 'x': bit_value+="xxxx"; break;
        case 'z': bit_value+="zzzz"; break;
          // clang-format on
        }
      }
      break;

    default:
      throw ebmc_errort() << "cannot convert literal " << value;
    }

    std::string fvalue;

    if(bits_given)
    {
      fvalue = bit_value;

      if(fvalue.size() > bits)
        fvalue.erase(0, fvalue.size() - bits); // cut off...
      else if(fvalue.size() < bits)
      {
        // extend appropriately
        char ext = '0';

        if(fvalue.size() != 0 && (fvalue[0] == 'x' || fvalue[0] == 'z'))
          ext = fvalue[0];

        // add missing bits
        fvalue = std::string(bits - fvalue.size(), ext) + fvalue;
      }
    }
    else
    {
      fvalue = bit_value;
      bits = fvalue.size();
    }

    if(four_valued)
    {
      // we do a 32-bit minimum if the number of bits isn't given
      if(!bits_given)
      {
        if(bits < 32)
        {
          // do sign extension
          char extension = is_signed ? fvalue.front() : '0';
          fvalue = std::string(32 - bits, extension) + fvalue;
          bits = 32;
        }
      }

      typet type;

      if(is_signed)
        type = verilog_signedbv_typet(bits);
      else
        type = verilog_unsignedbv_typet(bits);

      // stored as individual bits
      return constant_exprt{fvalue, type};
    }
    else // two valued
    {
      mp_integer int_value = binary2integer(fvalue, is_signed);

      // we do a 32-bit minimum if the number of bits isn't given
      if(!bits_given)
        if(bits < 32)
          bits = 32;

      typet type;

      if(is_signed)
        type = signedbv_typet(bits);
      else
        type = unsignedbv_typet(bits);

      // stored as bvrep
      return constant_exprt{integer2bvrep(int_value, bits), type};
    }
  }
  else
  {
    // base 10, never negative
    mp_integer int_value = string2integer(rest, base);

    if(!bits_given)
    {
      bits = address_bits(int_value + 1);
      // we do a 32-bit minimum
      if(bits < 32)
        bits = 32;
    }

    typet type;

    if(is_signed)
      type = signedbv_typet(bits);
    else
      type = unsignedbv_typet(bits);

    return constant_exprt{integer2bvrep(int_value, bits), type};
  }

  UNREACHABLE;
}
