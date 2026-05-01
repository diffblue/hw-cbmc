/*******************************************************************\

Module: BTOR2 Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BTOR_PARSER_H
#define CPROVER_BTOR_PARSER_H

#include <cstddef>
#include <iosfwd>
#include <map>
#include <string>
#include <vector>

/// A parsed BTOR2 line
struct btor2_linet
{
  std::size_t id = 0;
  std::string tag;
  std::size_t sort_id = 0;
  std::vector<std::ptrdiff_t> args; // signed: negative means negated
  std::vector<std::size_t> uargs;   // unsigned args (for indexed ops)
  std::string symbol;
};

/// Sort declaration
struct btor2_sortt
{
  enum class kindt
  {
    BITVEC,
    ARRAY
  };
  kindt kind;
  std::size_t width = 0;        // for bitvec
  std::size_t index_sort = 0;   // for array
  std::size_t element_sort = 0; // for array
};

/// Parsed BTOR2 model
struct btor2_modelt
{
  std::map<std::size_t, btor2_sortt> sorts;
  std::map<std::size_t, btor2_linet> nodes;
  std::vector<std::size_t> bad_properties;
  std::vector<std::size_t> constraints;
  std::vector<std::size_t> fair_properties;
  std::vector<std::size_t> outputs;
  std::vector<std::size_t> justice_properties;
};

/// Parse a BTOR2 file. Throws ebmc_errort on failure.
btor2_modelt btor2_parse(std::istream &);

/// Print parsed model for --show-parse
void btor2_show_parse(const btor2_modelt &, std::ostream &);

#endif // CPROVER_BTOR_PARSER_H
