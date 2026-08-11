/*******************************************************************\

Module: Verilog Parse Order

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Verilog Parse Order

#include "verilog_parse_order.h"

#include <util/message.h>

// This must match the definition that the scanner and the parser use.
#define YYSTYPE unsigned

#include "verilog_parser.h"
#include "verilog_y.tab.h"

#include <map>
#include <queue>

// scanner interface
int yyveriloglex();
extern char *yyverilogtext;
extern int yyverilogleng;

// The semantic value of the token that the scanner has produced. Note that
// this is an index into the expression stack of the parser that is current
// while scanning, and hence must not be allowed to outlive that parser.
extern YYSTYPE yyveriloglval;

/// Is the given token an identifier?
static bool is_identifier(int token)
{
  return token == TOK_NON_TYPE_IDENTIFIER || token == TOK_TYPE_IDENTIFIER ||
         token == TOK_PACKAGE_IDENTIFIER || token == TOK_CLASS_IDENTIFIER ||
         token == TOK_INTERFACE_IDENTIFIER;
}

/// The base name of the identifier token that the scanner has just returned.
static irep_idt identifier_base_name()
{
  std::string text{yyverilogtext, std::size_t(yyverilogleng)};

  // The backslash of an escaped identifier is not part of the name.
  if(!text.empty() && text[0] == '\\')
    return text.substr(1);

  return text;
}

verilog_package_usaget
verilog_scan_package_usage(std::istream &in, verilog_standardt standard)
{
  verilog_package_usaget result;

  // A throw-away scope table -- we do not record any identifiers -- and a
  // message handler that discards the scanner's diagnostics, which are
  // given when the file is parsed.
  verilog_scopest scopes;
  null_message_handlert message_handler;
  verilog_parsert verilog_parser{standard, scopes, message_handler};

  verilog_parser.in = &in;
  verilog_parser.grammar = verilog_parsert::LANGUAGE;

  // yyveriloglval indexes into the expression stack of the parser that is
  // current while scanning, and hence is meaningless once we are done. We
  // restore it, as the scanner writes it but the parser reads it, and the
  // parser that runs next starts out with an empty stack.
  auto saved_lval = yyveriloglval;

  verilog_scanner_init();

  // The token before the current one, and its base name when it is an
  // identifier.
  int previous_token = 0;
  irep_idt previous_base_name;

  while(true)
  {
    auto token = yyveriloglex();

    if(token == 0 || token == TOK_SCANNER_ERROR)
      break; // end of file, or a scanner error

    if(token == TOK_COLONCOLON && is_identifier(previous_token))
    {
      // 'some_name::' -- a reference to a package. This also matches a
      // reference to a class, which merely adds a spurious dependency
      // when a package of that name exists.
      result.references.insert(previous_base_name);
    }
    else if(is_identifier(token) && previous_token == TOK_PACKAGE)
    {
      // 'package some_name' -- a package declaration.
      result.declares.insert(identifier_base_name());
    }

    if(token == TOK_AUTOMATIC || token == TOK_STATIC)
    {
      // This is the optional lifetime in 'package automatic some_name;'.
      // Retain the 'package' keyword as the previous token.
    }
    else
    {
      previous_token = token;
      previous_base_name =
        is_identifier(token) ? identifier_base_name() : irep_idt{};
    }
  }

  yyveriloglval = saved_lval;

  return result;
}

std::vector<std::size_t>
verilog_parse_order(const std::vector<verilog_package_usaget> &usage)
{
  const auto number_of_files = usage.size();

  // Which files declare a given package? Note that a package may,
  // erroneously, be declared by more than one file.
  std::map<irep_idt, std::vector<std::size_t>> declared_by;

  for(std::size_t i = 0; i < number_of_files; i++)
    for(const auto &package : usage[i].declares)
      declared_by[package].push_back(i);

  // The files that must be parsed after file i, and the number of files
  // that must be parsed before file i and have not been emitted yet.
  std::vector<std::vector<std::size_t>> successors(number_of_files);
  std::vector<std::size_t> pending(number_of_files, 0);

  for(std::size_t i = 0; i < number_of_files; i++)
    for(const auto &package : usage[i].references)
    {
      auto d_it = declared_by.find(package);
      if(d_it == declared_by.end())
        continue; // no input file declares this package

      for(auto j : d_it->second)
      {
        if(j == i)
          continue; // a file may reference a package it declares itself

        successors[j].push_back(i);
        pending[i]++;
      }
    }

  // Topological sort, always taking the file that comes first on the
  // command line among those that are ready. Files without a dependency
  // hence retain their relative order.
  std::priority_queue<
    std::size_t,
    std::vector<std::size_t>,
    std::greater<std::size_t>>
    ready;

  for(std::size_t i = 0; i < number_of_files; i++)
    if(pending[i] == 0)
      ready.push(i);

  std::vector<std::size_t> result;
  result.reserve(number_of_files);
  std::vector<bool> emitted(number_of_files, false);

  while(result.size() != number_of_files)
  {
    std::size_t i;

    if(ready.empty())
    {
      // There is a cycle, which is illegal. Break it at the first file
      // that has not been emitted yet; the parser then reports the
      // offending reference to a package that is not declared yet.
      i = 0;
      while(emitted[i])
        i++;
    }
    else
    {
      i = ready.top();
      ready.pop();
    }

    emitted[i] = true;
    result.push_back(i);

    for(auto j : successors[i])
    {
      if(emitted[j])
        continue;

      DATA_INVARIANT(pending[j] != 0, "pending count must be consistent");
      if(--pending[j] == 0)
        ready.push(j);
    }
  }

  return result;
}
