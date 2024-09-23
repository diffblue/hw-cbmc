/*******************************************************************\

Module: Verilog Indexer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef VERILOG_INDEXER_H
#define VERILOG_INDEXER_H

#include <util/irep.h>

#include <verilog/verilog_standard.h>

#include <map>
#include <unordered_map>

/// This is a catalogue of Verilog identifiers by file.
/// See 1800-2017 Sec 3.13 Name spaces for an overview of
/// the name spaces.
class verilog_indexert
{
public:
  struct idt
  {
    using kindt = enum {
      UNKNOWN,
      PACKAGE,
      MODULE,
      UDP,
      INTERFACE,
      CLASS,
      CONFIG,
      TYPEDEF,
      FUNCTION,
      TASK,
      INSTANCE,
      BLOCK,
      NET,
      VARIABLE,
      PARAMETER,
      PORT
    };
    kindt kind = UNKNOWN;
    // identifier or identifier.identifier
    irep_idt name;
    irep_idt file_name;
    irep_idt module;
    std::size_t line_number;
    irep_idt instantiated_module; // for INSTANCE
    bool is_module() const
    {
      return kind == MODULE;
    }
    bool is_package() const
    {
      return kind == PACKAGE;
    }
    bool is_class() const
    {
      return kind == CLASS;
    }
    bool is_udp() const
    {
      return kind == UDP;
    }
    bool is_instance() const
    {
      return kind == INSTANCE;
    }
  };

  struct filet
  {
    std::size_t number_of_lines = 0;
    std::vector<idt> ids;
  };

  // The keys are the file names.
  using file_mapt = std::map<irep_idt, filet>;
  file_mapt file_map;

  /// add an idt
  void add(idt id)
  {
    auto file_name = id.file_name;
    file_map[file_name].ids.push_back(std::move(id));
  }

  /// index the given file
  void operator()(const irep_idt &file_name, verilog_standardt);

  using instancest =
    std::unordered_map<irep_idt, std::vector<idt>, irep_id_hash>;

  // statistics
  std::map<idt::kindt, std::size_t> total_number_of() const;
  std::size_t total_number_of_files() const;
  std::size_t total_number_of_symlinked_files() const;
  std::size_t total_number_of_lines() const;

protected:
  std::string preprocess(const std::string &file_name);
};

class cmdlinet;

int verilog_index(const cmdlinet &);

#endif // VERILOG_INDEXER_H
