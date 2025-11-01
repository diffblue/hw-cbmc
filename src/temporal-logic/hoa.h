/*******************************************************************\

Module: Hanoi Omega Automata (HOA) Format

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_HOA_H
#define CPROVER_TEMPORAL_LOGIC_HOA_H

#include <util/graph.h>
#include <util/irep.h>

#include <cstdint>
#include <list>
#include <map>
#include <string>

// https://adl.github.io/hoaf/hoaf.pdf
class hoat
{
public:
  // header
  using headert = std::list<std::pair<std::string, std::list<std::string>>>;
  headert header;

  // A HOA INT is non-negative and less than 2^31
  using intt = uint32_t;

  // body
  using labelt = irept;
  using acc_sigt = std::vector<std::string>;
  struct state_namet
  {
    intt number;
    labelt label; // in-state condition
    acc_sigt acc_sig;
    bool is_accepting() const
    {
      return !acc_sig.empty();
    }
  };
  struct edget
  {
    labelt label; // transition condition
    std::vector<intt> dest_states;
    acc_sigt acc_sig; // acceptance sets
  };
  using edgest = std::list<edget>;
  using bodyt = std::vector<std::pair<state_namet, edgest>>;
  bodyt body;

  hoat(headert _header, bodyt _body)
    : header(std::move(_header)), body(std::move(_body))
  {
  }

  static hoat from_string(const std::string &);
  void output(std::ostream &) const;

  friend std::ostream &operator<<(std::ostream &out, const hoat &hoa)
  {
    hoa.output(out);
    return out;
  }

  intt max_state_number() const;

  // atomic propositions
  using ap_mapt = std::map<intt, std::string>;

  // parses the AP header
  ap_mapt parse_AP() const;

  // convert into a graph
  struct graph_edget
  {
    labelt label;
  };

  grapht<graph_nodet<graph_edget>> graph() const;

  // Remove accepting states that are not part of a cycle.
  // These are irrelevant when using the standard Buechi
  // acceptance criterion.
  void buechi_acceptance_cleanup();
};

#endif // CPROVER_TEMPORAL_LOGIC_HOA_H
