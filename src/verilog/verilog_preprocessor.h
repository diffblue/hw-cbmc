#ifndef VERILOG_PREPROCESSOR_H
#define VERILOG_PREPROCESSOR_H

#include <util/invariant.h>
#include <util/irep.h>
#include <util/preprocessor.h>
#include <util/string_hash.h>

#include "verilog_preprocessor_tokenizer.h"

#include <filesystem>
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
    const std::string &_filename,
    const std::list<std::string> &_include_paths,
    const std::list<std::string> &_initial_defines)
    : preprocessort(_in, _out, _message_handler, _filename),
      include_paths(_include_paths),
      initial_defines(_initial_defines)
  {
    condition=true;
  }

  virtual ~verilog_preprocessort() { }

protected:
  // from the command line
  const std::list<std::string> &include_paths;
  const std::list<std::string> &initial_defines;

  using tokent = verilog_preprocessor_token_sourcet::tokent;

  struct definet
  {
    using parameterst = std::vector<std::string>;
    parameterst parameters;
    std::vector<tokent> tokens;
    definet() = default;
    explicit definet(std::vector<tokent> _tokens) : tokens(std::move(_tokens))
    {
    }
  };

  static std::string as_string(const std::vector<tokent> &);

  using definest = std::unordered_map<std::string, definet, string_hash>;
  definest defines;

  void directive();
  std::filesystem::path find_include_file(
    const std::filesystem::path &including_file,
    const std::string &given_filename,
    bool include_paths_only);
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

  // To synchronize the parser's line number
  std::size_t parser_line_no = 0;
  void emit_line_directive(unsigned level);

  // for include and for `define
  class contextt
  {
  protected:
    bool deallocate_in;
    std::istream *in;

  public:
    std::filesystem::path path;
    verilog_preprocessor_token_sourcet *tokenizer;

    std::string filename_as_string() const;

    // for `define with parameters
    define_argumentst define_arguments;

    contextt(
      bool _deallocate_in,
      std::istream *_in,
      std::filesystem::path _path)
      : deallocate_in(_deallocate_in),
        in(_in),
        path(std::move(_path)),
        tokenizer(new verilog_preprocessor_tokenizert(*in))
    {
    }

    explicit contextt(const std::vector<tokent> &tokens)
      : deallocate_in(false),
        in(nullptr),
        path(),
        tokenizer(new vector_token_sourcet(tokens))
    {
    }

    ~contextt()
    {
      delete tokenizer;
      if(deallocate_in)
        delete in;
    }

    source_locationt make_source_location() const;

    bool is_file() const
    {
      return !path.empty();
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
