/*******************************************************************\

Module: Verilog Indexer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_indexer.h"

#include <util/unicode.h>

#include "verilog_preprocessor.h"

#include <fstream>

void verilog_indexert::operator()(const irep_idt &file_name)
{
  // run the preprocessor
  const auto preprocessed_string = preprocess(id2string(file_name));
  std::istringstream preprocessed(preprocessed_string);

  // set up the tokenizer

  // now parse
}

std::string verilog_indexert::preprocess(const std::string &file_name)
{
  std::stringstream preprocessed;

  auto in_stream = std::ifstream(widen_if_needed(file_name));

  if(!in_stream)
  {
    // We deliberately fail silently.
    // Errors on invalid file names are expected to be raised
    // later.
    return std::string();
  }

  null_message_handlert message_handler;
  verilog_preprocessort preprocessor(
    in_stream, preprocessed, message_handler, file_name);

  preprocessor.preprocessor();

  return preprocessed.str();
}

void verilog_indexert::parsert::rDescription()
{
}
