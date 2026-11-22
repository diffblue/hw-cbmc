/*******************************************************************\

Module: Verilog Bit-Level Layout

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// The mapping from the elements of Verilog types (vector bits, array
/// elements, struct and union members) to bit positions in their bit-level
/// representation. Bit 0 is the least significant bit.
///
/// The layout is used by the read side (to_bitvector/from_bitvector in
/// verilog_lowering.cpp) and by the write side (verilog_rtl.cpp), and
/// must be the same for both. This file is the only place that defines it.
///
/// The functions only compute positions; they do not construct
/// expressions. Positions are relative to the start of the type that is
/// given; for out-of-range indices, the results lie outside of the type,
/// and the caller decides what that means (1800-2017 7.4.6).

#ifndef CPROVER_VERILOG_VERILOG_LAYOUT_H
#define CPROVER_VERILOG_VERILOG_LAYOUT_H

#include <util/mp_arith.h>
#include <util/std_types.h>

#include <optional>
#include <vector>

class verilog_array_typet;

/// A contiguous range of bits, given as zero-based bit positions
/// [lower, upper], both inclusive.
struct verilog_bit_ranget
{
  mp_integer lower, upper;

  mp_integer width() const
  {
    return upper - lower + 1;
  }
};

/// The bits of a vector of the given \p width that hold the bits with
/// the declared indices \p lo..\p hi, where lo <= hi.
///
/// For a decreasing range [l:r] with l>=r, the declared index i is bit
/// i-offset. For an increasing range [l:r] with l<r, index l is the most
/// significant bit, and the declared index i is bit (width-1)-(i-offset)
/// (1800-2017 7.4.1, 11.5.1).
verilog_bit_ranget verilog_vector_bit_range(
  const mp_integer &width,
  const mp_integer &offset,
  bool increasing,
  const mp_integer &lo,
  const mp_integer &hi);

/// Is the element with array index 0 of the given array the most
/// significant one? This is the case for packed arrays with an increasing
/// range (1800-2017 7.4.1); for all other arrays, the element with array
/// index 0 occupies the least significant bits.
bool verilog_array_element_zero_is_msb(const array_typet &);

/// The lowest bit of the element with the given (zero-based) array index
/// of an array with constant size, as laid out by
/// \ref verilog_array_element_zero_is_msb.
mp_integer verilog_array_element_lower_bit(
  const array_typet &,
  const mp_integer &array_index);

/// The array index of the element with the given declared index of an
/// unpacked array. Unpacked arrays store their elements starting from
/// the left index of the declared range, i.e., the element with the left
/// index has array index 0.
mp_integer verilog_unpacked_array_element_index(
  const verilog_array_typet &,
  const mp_integer &declared_index);

/// The lowest bit of the elements with the declared indices \p lo..\p hi,
/// where lo <= hi, of a packed array. For an increasing range, the
/// element with the lowest declared index is the most significant; for a
/// decreasing range, it is the least significant (1800-2017 7.4.1).
mp_integer verilog_packed_array_lower_bit(
  const verilog_array_typet &,
  const mp_integer &lo,
  const mp_integer &hi);

/// The lowest bit of each component of a struct, in the order of the
/// components. The first component of a packed struct is the most
/// significant (1800-2017 7.2.1). All components of a union start at
/// bit 0, and hence the result is only meaningful for structs.
std::vector<mp_integer> verilog_struct_component_lower_bits(const typet &);

/// The bits of the struct or union member with the given name. Returns
/// nullopt if the type is neither a struct nor a union, or if it has no
/// such member.
std::optional<verilog_bit_ranget>
verilog_member_bit_range(const typet &compound, const irep_idt &member_name);

#endif // CPROVER_VERILOG_VERILOG_LAYOUT_H
