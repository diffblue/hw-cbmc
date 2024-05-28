/*******************************************************************\

Module: VCD Parser

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <iosfwd>
#include <map>
#include <string>
#include <vector>

class vcdt
{
public:
  struct vart
  {
    std::string type;
    std::size_t size;
    std::string id;
    std::string reference;
  };

  using var_mapt = std::map<std::string, vart>;
  var_mapt var_map;

  using value_mapt = std::map<std::string, std::string>;

  struct statet
  {
    explicit statet(std::string t) : simulation_time(std::move(t))
    {
    }

    std::string simulation_time;
    value_mapt changes;
  };

  std::vector<statet> states;

  void simulation_time(const std::string &t)
  {
    states.push_back(statet(t));
  }

  void value_change(std::string value, const std::string &identifier)
  {
    if(states.empty())
      simulation_time("");
    states.back().changes[identifier] = std::move(value);
  }

  // Expand the differential trace into a trace of full states,
  // including all unchanged values.
  std::vector<statet> full_trace() const;
};

std::ostream &operator<<(std::ostream &, const vcdt::statet &);

vcdt vcd_parser(std::istream &);
