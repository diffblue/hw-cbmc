/*******************************************************************\

Module: Output File Container

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "output_file.h"

#include <util/unicode.h>

#include "ebmc_error.h"

#include <fstream>
#include <iostream>

output_filet::output_filet(std::string __file_name)
  : _name(std::move(__file_name))
{
  if(_name == "-")
  {
    _stream = &std::cout;
    delete_required = false;
    _name = "stdout";
  }
  else
  {
    _stream = new std::ofstream(widen_if_needed(_name));
    if(!_stream)
      throw ebmc_errort() << "failed to open " << _name;
    delete_required = true;
  }
}

output_filet::~output_filet()
{
  if(delete_required)
    delete _stream;
}
