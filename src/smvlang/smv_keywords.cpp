/*******************************************************************\

Module: SMV Keywords

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "smv_keywords.h"

#include <unordered_set>

bool is_smv_keyword(const irep_idt &id)
{
  static const std::unordered_set<irep_idt, irep_id_hash> keywords = {
    // Section keywords
    "MODULE",
    "DEFINE",
    "MDEFINE",
    "CONSTANTS",
    "VAR",
    "IVAR",
    "FROZENVAR",
    "INIT",
    "TRANS",
    "INVAR",
    "SPEC",
    "CTLSPEC",
    "LTLSPEC",
    "PSLSPEC",
    "COMPUTE",
    "NAME",
    "INVARSPEC",
    "FAIRNESS",
    "JUSTICE",
    "COMPASSION",
    "ISA",
    "ASSIGN",
    "CONSTRAINT",
    "SIMPWFF",
    "CTLWFF",
    "LTLWFF",
    "PSLWFF",
    "COMPWFF",
    "MIN",
    "MAX",
    "MIRROR",
    "PRED",
    "PREDICATES",
    // Type keywords
    "process",
    "array",
    "of",
    "boolean",
    "integer",
    "real",
    "word",
    "word1",
    "bool",
    "signed",
    "unsigned",
    "extend",
    "resize",
    "sizeof",
    "toint",
    "uwconst",
    "swconst",
    // CTL operators
    "EX",
    "AX",
    "EF",
    "AF",
    "EG",
    "AG",
    "E",
    "F",
    "O",
    "G",
    "H",
    "X",
    "Y",
    "Z",
    "A",
    "U",
    "S",
    "V",
    "T",
    "BU",
    "EBF",
    "ABF",
    "EBG",
    "ABG",
    // Other keywords
    "case",
    "esac",
    "mod",
    "next",
    "init",
    "union",
    "in",
    "xor",
    "xnor",
    "self",
    "TRUE",
    "FALSE",
    "count",
    "abs",
    "max",
    "min",
  };

  return keywords.count(id) != 0;
}
