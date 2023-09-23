#ifndef VERILOG_PREPROCESSOR_H
#define VERILOG_PREPROCESSOR_H

#include <util/invariant.h>
#include <util/irep.h>
#include <util/preprocessor.h>
#include <util/string_hash.h>

#include "verilog_preprocessor_tokenizer.h"

#include <list>

class verilog_preprocessort:public preprocessort
{
public:
  virtual void preprocessor();

  verilog_preprocessort(
    std::istream &_in,
    std::ostream &_out,
    message_handlert &_message_handler,
    const std::string &_filename):
    preprocessort(_in, _out, _message_handler, _filename)
  {
    condition=true;
  }

  virtual ~verilog_preprocessort() { }

protected:
  typedef std::unordered_map<std::string, std::string, string_hash>
    definest;
    
  definest defines;
  
  virtual void directive();
  virtual void replace_macros(std::string &s);
  virtual void include(const std::string &filename);

  // for ifdef, else, endif
  
  bool condition;
  
  class conditionalt
  {
  public:
    bool condition;
    bool previous_condition;
    bool else_part;
    
    conditionalt()
    { else_part=false; }
     
    bool get_cond()
    {
      return previous_condition &&
             (else_part?(!condition):condition);
    }
  };

  std::list<conditionalt> conditionals;

  // for include

  class filet
  {
  protected:
    bool close;
    std::istream *in;
    std::string filename;

  public:
    verilog_preprocessor_tokenizert tokenizer;

    filet(bool _close, std::istream *_in, std::string _filename)
      : close(_close), in(_in), filename(std::move(_filename)), tokenizer(*in)
    {
    }

    ~filet()
    {
      if(close)
        delete in;
    }

    void print_line_directive(std::ostream &out, unsigned level) const
    {
      out << "`line " << tokenizer.line_no() << " \"" << filename << "\" "
          << level << '\n';
    }

    source_locationt make_source_location() const;
  };

  std::list<filet> files;

  // the topmost tokenizer
  verilog_preprocessor_tokenizert &tokenizer()
  {
    PRECONDITION(!files.empty());
    return files.back().tokenizer;
  }
};

#endif
