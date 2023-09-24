#ifndef VERILOG_PREPROCESSOR_H
#define VERILOG_PREPROCESSOR_H

#include <util/invariant.h>
#include <util/irep.h>
#include <util/preprocessor.h>
#include <util/string_hash.h>

#include "verilog_preprocessor_tokenizer.h"

#include <list>
#include <map>

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
  using tokent = verilog_preprocessor_token_sourcet::tokent;

  struct definet
  {
    using parameterst = std::vector<std::string>;
    parameterst parameters;
    std::vector<tokent> tokens;
  };

  static std::string as_string(const std::vector<tokent> &);

  using definest = std::unordered_map<std::string, definet, string_hash>;
  definest defines;

  void directive();
  void include(const std::string &filename);
  definet::parameterst parse_define_parameters();

  using define_argumentst = std::map<std::string, std::vector<tokent>>;
  define_argumentst parse_define_arguments(const definet &);

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

  class vector_token_sourcet : public verilog_preprocessor_token_sourcet
  {
  public:
    vector_token_sourcet(const std::vector<tokent> &_tokens)
      : tokens(_tokens), pos(tokens.begin())
    {
    }

  protected:
    const std::vector<tokent> &tokens;
    std::vector<tokent>::const_iterator pos;
    void get_token_from_stream() override;
  };

  // for include and for `define
  class contextt
  {
  protected:
    bool deallocate_in;
    std::istream *in;
    std::string filename;

  public:
    verilog_preprocessor_token_sourcet *tokenizer;

    // for `define with parameters
    define_argumentst define_arguments;

    contextt(bool _deallocate_in, std::istream *_in, std::string _filename)
      : deallocate_in(_deallocate_in),
        in(_in),
        filename(std::move(_filename)),
        tokenizer(new verilog_preprocessor_tokenizert(*in))
    {
    }

    explicit contextt(const std::vector<tokent> &tokens)
      : deallocate_in(false),
        in(nullptr),
        filename(),
        tokenizer(new vector_token_sourcet(tokens))
    {
    }

    ~contextt()
    {
      delete tokenizer;
      if(deallocate_in)
        delete in;
    }

    void print_line_directive(std::ostream &out, unsigned level) const
    {
      out << "`line " << tokenizer->line_no() << " \"" << filename << "\" "
          << level << '\n';
    }

    source_locationt make_source_location() const;

    bool is_file() const
    {
      return !filename.empty();
    }
  };

  std::list<contextt> context_stack;

  // the topmost context
  contextt &context()
  {
    PRECONDITION(!context_stack.empty());
    return context_stack.back();
  }

  // the topmost tokenizer
  verilog_preprocessor_token_sourcet &tokenizer()
  {
    return *(context().tokenizer);
  }
};

#endif
