/*******************************************************************\

Module: BTOR2 Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "btor_parser.h"

#include <ebmc/ebmc_error.h>

#include <iostream>
#include <set>
#include <sstream>

/// Tags that take no sort and a single nid argument
static const std::set<std::string> signal_tags =
  {"bad", "constraint", "fair", "output"};

/// Tags that take a sort and two nid arguments
static const std::set<std::string> init_next_tags = {"init", "next"};

/// Indexed operators (take sort, nid, then one or two uint indices)
static const std::set<std::string> indexed_op_tags = {"sext", "uext", "slice"};

/// Tags that declare a node with a sort
static const std::set<std::string> input_tags =
  {"input", "one", "ones", "zero", "const", "constd", "consth", "state"};

btor2_modelt btor2_parse(std::istream &in)
{
  btor2_modelt model;
  std::string line;
  std::size_t line_number = 0;

  while(std::getline(in, line))
  {
    line_number++;

    // skip empty lines and comments
    if(line.empty() || line[0] == ';')
      continue;

    std::istringstream ss(line);

    std::size_t id;
    std::string tag;

    if(!(ss >> id >> tag))
    {
      throw ebmc_errort{} << "BTOR2 parse error on line " << line_number;
    }

    // Sort declaration: <sid> sort (bitvec <width> | array <sid> <sid>)
    if(tag == "sort")
    {
      std::string sort_kind;
      if(!(ss >> sort_kind))
        throw ebmc_errort{} << "BTOR2: expected sort kind on line "
                            << line_number;

      btor2_sortt sort;
      if(sort_kind == "bitvec")
      {
        sort.kind = btor2_sortt::kindt::BITVEC;
        if(!(ss >> sort.width))
          throw ebmc_errort{} << "BTOR2: expected width on line "
                              << line_number;
      }
      else if(sort_kind == "array")
      {
        sort.kind = btor2_sortt::kindt::ARRAY;
        if(!(ss >> sort.index_sort >> sort.element_sort))
          throw ebmc_errort{} << "BTOR2: expected array sorts on line "
                              << line_number;
      }
      else
      {
        throw ebmc_errort{} << "BTOR2: unknown sort kind '" << sort_kind
                            << "' on line " << line_number;
      }

      model.sorts[id] = sort;
      continue;
    }

    btor2_linet node;
    node.id = id;
    node.tag = tag;

    if(signal_tags.count(tag))
    {
      // <nid> bad/constraint/fair/output <nid>
      std::ptrdiff_t arg;
      if(!(ss >> arg))
        throw ebmc_errort{} << "BTOR2: expected argument on line "
                            << line_number;
      node.args.push_back(arg);

      if(tag == "bad")
        model.bad_properties.push_back(id);
      else if(tag == "constraint")
        model.constraints.push_back(id);
      else if(tag == "fair")
        model.fair_properties.push_back(id);
      else if(tag == "output")
        model.outputs.push_back(id);
    }
    else if(tag == "justice")
    {
      // <nid> justice <num> (<nid>)+
      std::size_t count;
      if(!(ss >> count))
        throw ebmc_errort{} << "BTOR2: expected count on line " << line_number;
      for(std::size_t i = 0; i < count; i++)
      {
        std::ptrdiff_t arg;
        if(!(ss >> arg))
          throw ebmc_errort{} << "BTOR2: expected justice arg on line "
                              << line_number;
        node.args.push_back(arg);
      }
      model.justice_properties.push_back(id);
    }
    else if(input_tags.count(tag))
    {
      // <nid> (input|state|one|ones|zero) <sid>
      // <nid> const <sid> <binary>
      // <nid> constd <sid> <decimal>
      // <nid> consth <sid> <hex>
      if(!(ss >> node.sort_id))
        throw ebmc_errort{} << "BTOR2: expected sort on line " << line_number;

      if(tag == "const" || tag == "constd" || tag == "consth")
      {
        // Store the constant value as the symbol
        std::string val;
        if(!(ss >> val))
          throw ebmc_errort{} << "BTOR2: expected value on line "
                              << line_number;
        node.symbol = val;
      }
    }
    else if(init_next_tags.count(tag))
    {
      // <nid> init/next <sid> <nid> <nid>
      std::ptrdiff_t arg1, arg2;
      if(!(ss >> node.sort_id >> arg1 >> arg2))
        throw ebmc_errort{} << "BTOR2: expected args on line " << line_number;
      node.args.push_back(arg1);
      node.args.push_back(arg2);
    }
    else if(indexed_op_tags.count(tag))
    {
      // <nid> sext/uext <sid> <nid> <uint>
      // <nid> slice <sid> <nid> <uint> <uint>
      std::ptrdiff_t arg;
      if(!(ss >> node.sort_id >> arg))
        throw ebmc_errort{} << "BTOR2: expected args on line " << line_number;
      node.args.push_back(arg);

      std::size_t idx1;
      if(!(ss >> idx1))
        throw ebmc_errort{} << "BTOR2: expected index on line " << line_number;
      node.uargs.push_back(idx1);

      if(tag == "slice")
      {
        std::size_t idx2;
        if(!(ss >> idx2))
          throw ebmc_errort{} << "BTOR2: expected index on line "
                              << line_number;
        node.uargs.push_back(idx2);
      }
    }
    else
    {
      // Generic operator: <nid> <op> <sid> <nid> [<nid> [<nid>]]
      if(!(ss >> node.sort_id))
        throw ebmc_errort{} << "BTOR2: expected sort on line " << line_number;

      std::ptrdiff_t arg;
      while(ss >> arg)
        node.args.push_back(arg);
    }

    // Read optional symbol (for input/state nodes that haven't
    // consumed the rest of the line)
    if(
      node.symbol.empty() && input_tags.count(tag) && tag != "const" &&
      tag != "constd" && tag != "consth")
    {
      std::string sym;
      if(ss >> sym && !sym.empty() && sym[0] != ';')
        node.symbol = sym;
    }

    model.nodes[id] = std::move(node);
  }

  return model;
}

void btor2_show_parse(const btor2_modelt &model, std::ostream &out)
{
  out << "BTOR2 model\n";
  out << "  Sorts: " << model.sorts.size() << '\n';
  out << "  Nodes: " << model.nodes.size() << '\n';
  out << "  Bad properties: " << model.bad_properties.size() << '\n';
  out << "  Constraints: " << model.constraints.size() << '\n';
  out << "  Fair properties: " << model.fair_properties.size() << '\n';
  out << "  Outputs: " << model.outputs.size() << '\n';
  out << "  Justice properties: " << model.justice_properties.size() << '\n';

  for(auto &[id, sort] : model.sorts)
  {
    out << "  Sort " << id << ": ";
    if(sort.kind == btor2_sortt::kindt::BITVEC)
      out << "bitvec " << sort.width;
    else
      out << "array " << sort.index_sort << " " << sort.element_sort;
    out << '\n';
  }

  for(auto &[id, node] : model.nodes)
  {
    out << "  " << id << " " << node.tag;
    if(node.sort_id != 0)
      out << " sort=" << node.sort_id;
    for(auto arg : node.args)
      out << " " << arg;
    for(auto u : node.uargs)
      out << " [" << u << "]";
    if(!node.symbol.empty())
      out << " '" << node.symbol << "'";
    out << '\n';
  }
}
