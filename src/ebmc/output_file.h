/*******************************************************************\

Module: Output File Container

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef EBMC_OUTPUT_FILE_H
#define EBMC_OUTPUT_FILE_H

#include <iosfwd>
#include <string>

class output_filet final
{
public:
  /// Create a stream to the given file name,
  /// our stdout if "-".
  /// Throws ebmc_errort() if the file cannot be opened.
  explicit output_filet(std::string __file_name);
  ~output_filet();

  std::ostream &stream()
  {
    return *_stream;
  }

  // the name of the file, or "stdout"
  const std::string &name()
  {
    return _name;
  }

protected:
  std::string _name;
  bool delete_required;
  std::ostream *_stream;
};

#endif
