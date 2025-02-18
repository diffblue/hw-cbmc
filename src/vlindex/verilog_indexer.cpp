/*******************************************************************\

Module: Verilog Indexer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_indexer.h"

#include <util/cmdline.h>
#include <util/cout_message.h>
#include <util/suffix.h>
#include <util/unicode.h>

#include <verilog/verilog_preprocessor.h>

#include "vlindex_parser.h"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <unordered_map>
#include <unordered_set>

std::size_t verilog_indexert::total_number_of_files() const
{
  return file_map.size();
}

std::size_t verilog_indexert::total_number_of_symlinked_files() const
{
  std::size_t result = 0;
  for(auto &[path, _] : file_map)
  {
    if(std::filesystem::is_symlink(id2string(path)))
      result++;
  }
  return result;
}

std::map<verilog_indexert::idt::kindt, std::size_t>
verilog_indexert::total_number_of() const
{
  std::map<verilog_indexert::idt::kindt, std::size_t> result;
  for(auto &[_, file] : file_map)
    for(auto &id : file.ids)
      result[id.kind]++;
  return result;
}

std::size_t verilog_indexert::total_number_of_lines() const
{
  std::size_t sum = 0;
  for(auto &[_, file] : file_map)
    sum += file.number_of_lines;
  return sum;
}

void verilog_indexert::operator()(
  const irep_idt &file_name,
  enum verilog_standardt standard)
{
  // run the preprocessor
  const auto preprocessed_string = preprocess(id2string(file_name));
  std::istringstream preprocessed(preprocessed_string);

  // set up the tokenizer
  console_message_handlert message_handler;
  verilog_indexer_parsert parser(
    preprocessed, *this, standard, message_handler);
  verilog_scanner_init();

  // now parse
  parser.rDescription();
  file_map[file_name].number_of_lines = parser.verilog_parser.get_line_no();
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

  console_message_handlert message_handler;
  verilog_preprocessort preprocessor(
    in_stream, preprocessed, message_handler, file_name, {}, {});

  try
  {
    preprocessor.preprocessor();
  }
  catch(...)
  {
  }

  return preprocessed.str();
}

std::vector<std::filesystem::path> verilog_files()
{
  std::vector<std::filesystem::path> result;

  auto current = std::filesystem::current_path();

  for(auto &entry : std::filesystem::recursive_directory_iterator(current))
    if(!is_directory(entry.path()))
      if(
#ifdef _WIN32
        has_suffix(narrow(entry.path()), ".v") ||
        has_suffix(narrow(entry.path()), ".sv"))
#else
        has_suffix(entry.path(), ".v") || has_suffix(entry.path(), ".sv"))
#endif
      {
        result.push_back(std::filesystem::relative(entry.path()));
      }

  return result;
}

void show_module_hierarchy_rec(
  const irep_idt &module,
  std::size_t indent,
  const verilog_indexert::instancest &instances)
{
  auto m_it = instances.find(module);
  if(m_it != instances.end())
  {
    // We output in the order found in the file,
    // but show the sub-instances of any module only once.
    std::unordered_set<irep_idt> done;
    for(auto &instance : m_it->second)
    {
      std::cout << std::string(indent * 2, ' ') << instance.instantiated_module
                << ' ' << instance.name << '\n';
      if(done.insert(instance.instantiated_module).second)
        show_module_hierarchy_rec(
          instance.instantiated_module, indent + 1, instances);
    }
  }
}

void sort_alphabetically(std::vector<verilog_indexert::idt> &ids)
{
  using idt = verilog_indexert::idt;
  std::sort(
    ids.begin(),
    ids.end(),
    [](const idt &a, const idt &b) { return a.name.compare(b.name) < 0; });
}

void show_module_hierarchy(const verilog_indexert &indexer)
{
  std::unordered_set<irep_idt, irep_id_hash> instantiated_modules;
  // module -> list of instances
  verilog_indexert::instancest instances;

  for(const auto &[_, file] : indexer.file_map)
    for(const auto &id : file.ids)
      if(id.is_instance())
      {
        instantiated_modules.insert(id.instantiated_module);
        instances[id.module].push_back(id);
      }

  // identify root modules
  std::vector<irep_idt> root_modules;
  for(auto &[_, file] : indexer.file_map)
    for(const auto &id : file.ids)
      if(
        id.is_module() &&
        instantiated_modules.find(id.name) == instantiated_modules.end())
      {
        root_modules.push_back(id.name);
      }

  // sort those alphabetically
  std::sort(
    root_modules.begin(),
    root_modules.end(),
    [](const irep_idt &a, const irep_idt &b) { return a.compare(b) < 0; });

  for(auto &root : root_modules)
  {
    std::cout << root << '\n';
    show_module_hierarchy_rec(root, 1, instances);
  }
}

void show_kind(
  verilog_indexert::idt::kindt kind,
  const verilog_indexert &indexer)
{
  std::vector<verilog_indexert::idt> ids;

  for(const auto &[_, file] : indexer.file_map)
    for(const auto &id : file.ids)
      if(id.kind == kind)
        ids.push_back(id);

  sort_alphabetically(ids);

  for(const auto &id : ids)
  {
    std::cout << id.name << ' ' << id.file_name << " line " << id.line_number
              << '\n';
  }
}

int verilog_index(const cmdlinet &cmdline)
{
  verilog_indexert indexer;

  verilog_standardt standard = [&cmdline]()
  {
    if(cmdline.isset("1800-2017"))
      return verilog_standardt::SV2017;
    else if(cmdline.isset("1800-2012"))
      return verilog_standardt::SV2012;
    else if(cmdline.isset("1800-2009"))
      return verilog_standardt::SV2009;
    else if(cmdline.isset("1800-2005"))
      return verilog_standardt::SV2005;
    else if(cmdline.isset("1364-2005"))
      return verilog_standardt::V2005;
    else if(cmdline.isset("1364-2001"))
      return verilog_standardt::V2001;
    else if(cmdline.isset("1364-2001-noconfig"))
      return verilog_standardt::V2001_NOCONFIG;
    else if(cmdline.isset("1364-1995"))
      return verilog_standardt::V1995;
    else // default
      return verilog_standardt::SV2017;
  }();

  // Are we given file names on the command line?
  if(cmdline.args.empty())
  {
    // No, find all .v and .sv files
    auto files = verilog_files();

    for(const auto &file : files)
    {
#ifdef _WIN32
      indexer(narrow(file), standard);
#else
      indexer(std::string(file), standard);
#endif
    }
  }
  else
  {
    // Yes, index the given files
    for(const auto &file : cmdline.args)
    {
      indexer(file, standard);
    }
  }

  if(cmdline.isset("hierarchy"))
  {
    show_module_hierarchy(indexer);
  }
  else if(cmdline.isset("modules"))
  {
    // Show the modules.
    show_kind(verilog_indexert::idt::kindt::MODULE, indexer);
  }
  else if(cmdline.isset("packages"))
  {
    // Show the packages.
    show_kind(verilog_indexert::idt::kindt::PACKAGE, indexer);
  }
  else if(cmdline.isset("interfaces"))
  {
    // Show the interfaces.
    show_kind(verilog_indexert::idt::kindt::INTERFACE, indexer);
  }
  else if(cmdline.isset("checkers"))
  {
    // Show the checker.
    show_kind(verilog_indexert::idt::kindt::CHECKER, indexer);
  }
  else if(cmdline.isset("classes"))
  {
    // Show the interfaces.
    show_kind(verilog_indexert::idt::kindt::CLASS, indexer);
  }
  else if(cmdline.isset("udps"))
  {
    // Show the interfaces.
    show_kind(verilog_indexert::idt::kindt::UDP, indexer);
  }
  else if(cmdline.isset("instances"))
  {
    // Show the module instances.
    show_kind(verilog_indexert::idt::kindt::INSTANCE, indexer);
  }
  else if(cmdline.isset("functions"))
  {
    // Show the functions.
    show_kind(verilog_indexert::idt::kindt::FUNCTION, indexer);
  }
  else if(cmdline.isset("tasks"))
  {
    // Show the module instances.
    show_kind(verilog_indexert::idt::kindt::TASK, indexer);
  }
  else if(cmdline.isset("sequences"))
  {
    // Show the sequences.
    show_kind(verilog_indexert::idt::kindt::SEQUENCE, indexer);
  }
  else if(cmdline.isset("properties"))
  {
    // Show the properties.
    show_kind(verilog_indexert::idt::kindt::PROPERTY, indexer);
  }
  else
  {
    auto total_number_of = indexer.total_number_of();
    using idt = verilog_indexert::idt;
    std::cout << "Number of files...........: "
              << indexer.total_number_of_files() << '\n';
    std::cout << "Number of symlinked files.: "
              << indexer.total_number_of_symlinked_files() << '\n';
    std::cout << "Number of lines...........: "
              << indexer.total_number_of_lines() << '\n';
    std::cout << "Number of modules.........: " << total_number_of[idt::MODULE]
              << '\n';
    std::cout << "Number of UDPs............: " << total_number_of[idt::UDP]
              << '\n';
    std::cout << "Number of checkers........: " << total_number_of[idt::CHECKER]
              << '\n';
    std::cout << "Number of classes.........: " << total_number_of[idt::CLASS]
              << '\n';
    std::cout << "Number of packages........: " << total_number_of[idt::PACKAGE]
              << '\n';
    std::cout << "Number of interfaces......: "
              << total_number_of[idt::INTERFACE] << '\n';
    std::cout << "Number of functions.......: "
              << total_number_of[idt::FUNCTION] << '\n';
    std::cout << "Number of tasks...........: " << total_number_of[idt::TASK]
              << '\n';
    std::cout << "Number of properties......: "
              << total_number_of[idt::PROPERTY] << '\n';
    std::cout << "Number of sequences.......: "
              << total_number_of[idt::SEQUENCE] << '\n';
    std::cout << "Number of module instances: "
              << total_number_of[idt::INSTANCE] << '\n';
    std::cout << "Number of configurations..: " << total_number_of[idt::CONFIG]
              << '\n';
  }

  return 0;
}
