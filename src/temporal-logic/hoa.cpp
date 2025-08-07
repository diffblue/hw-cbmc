/*******************************************************************\

Module: Hanoi Omega Automata (HOA) Format

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "hoa.h"

#include <util/arith_tools.h>
#include <util/string2int.h>

#include <ebmc/ebmc_error.h>

#include <ostream>
#include <sstream>

class hoa_tokenizert
{
public:
  explicit hoa_tokenizert(std::istream &_in) : in(_in)
  {
  }

  struct tokent
  {
    tokent() = default;
    explicit tokent(char ch) : text(1, ch)
    {
    }

    std::string text, string;
    bool is_string() const
    {
      return text.empty();
    }
    bool is_state() const
    {
      return text == "State:";
    }
    bool is_body() const
    {
      return text == "--BODY--";
    }
    bool is_end() const
    {
      return text == "--END--";
    }
    bool is_headername() const
    {
      // Headernames end on a colon, and are not quoted strings.
      return !text.empty() && text.back() == ':';
    }
  };

  const tokent &peek()
  {
    if(!token_opt.has_value())
      token_opt = get_token(in);
    return token_opt.value();
  }

  tokent consume()
  {
    if(token_opt.has_value())
    {
      auto value = std::move(token_opt.value());
      token_opt = {};
      return value;
    }
    else
    {
      return get_token(in);
    }
  }

protected:
  std::istream &in;
  static tokent get_token(std::istream &);
  std::optional<tokent> token_opt;
  static bool is_whitespace(char ch)
  {
    return ch == ' ' || ch == '\r' || ch == '\n' || ch == '\t';
  }
};

hoa_tokenizert::tokent hoa_tokenizert::get_token(std::istream &in)
{
  while(true)
  {
    char ch;

    if(!in.get(ch))
      throw ebmc_errort() << "EOF while reading HOA";

    if(is_whitespace(ch))
    {
      // ignore
    }
    else if(ch == '/')
    {
      if(in.peek() == '*')
      {
        // comment; these may be nested
        in.get(ch); // eat *
        std::size_t nesting = 1;
        while(true)
        {
          if(!in.get(ch))
            throw ebmc_errort() << "EOF while reading HOA comment";
          if(ch == '*' && in.peek() == '/')
          {
            in.get(ch); // eat /
            nesting--;
            if(nesting == 0)
              break; // done
          }
          else if(ch == '/' && in.peek() == '*')
          {
            in.get(ch); // eat *
            nesting++;
          }
        }
      }
      else
      {
        // just a /
        return tokent{ch};
      }
    }
    else if(ch == '"')
    {
      // quoted string
      tokent token;
      while(true)
      {
        if(!in.get(ch))
          throw ebmc_errort() << "EOF while reading HOA string";

        if(ch == '"')
          return token;
        else
          token.string += ch;
      }
    }
    else if(isalnum(ch) || ch == '_' || ch == '@' || ch == '-')
    {
      // BOOLEAN, IDENTIFIER, ANAME, HEADERNAME, INT, --BODY--, --END--
      // Dots appear to be allowed in identifiers, in contrast to the definition.
      tokent token;
      token.text += ch;
      auto cont = [](char ch) {
        return isalnum(ch) || ch == '_' || ch == '-' || ch == ':' || ch == '.';
      };
      while(cont(in.peek()))
      {
        in.get(ch);
        token.text += ch;
      }
      return token;
    }
    else
    {
      // single-character token, say {}()[]
      return tokent{ch};
    }
  }
}

hoat::intt hoat::max_state_number() const
{
  intt max = 0;

  for(auto &state : body)
    max = std::max(max, state.first.number);

  return max;
}

class hoa_parsert
{
public:
  explicit hoa_parsert(hoa_tokenizert &_tokenizer) : tokenizer(_tokenizer)
  {
  }

  hoa_tokenizert &tokenizer;

  using headert = hoat::headert;
  using bodyt = hoat::bodyt;
  using edgest = hoat::edgest;
  using edget = hoat::edget;
  using labelt = hoat::labelt;
  using state_namet = hoat::state_namet;
  using acc_sigt = hoat::acc_sigt;

  headert parse_header();
  bodyt parse_body();
  state_namet parse_state_name();
  edgest parse_edges();
  edget parse_edge();
  labelt parse_label();
  labelt parse_label_expr()
  {
    return parse_label_expr_or();
  }
  labelt parse_label_expr_or();
  labelt parse_label_expr_and();
  labelt parse_label_expr_primary();
  acc_sigt parse_acc_sig();
  hoat::intt parse_int();
};

hoat hoat::from_string(const std::string &src)
{
  std::istringstream in(src);
  hoa_tokenizert tokenizer(in);
  hoa_parsert parser(tokenizer);

  auto header = parser.parse_header();
  auto body = parser.parse_body();

  return hoat{header, body};
}

hoat::intt hoa_parsert::parse_int()
{
  auto text = tokenizer.consume().text;
  auto int_opt = string2optional<hoat::intt>(text);
  if(!int_opt.has_value())
    throw ebmc_errort() << "HOA-parser failed to parse INT";
  return int_opt.value();
}

hoat::headert hoa_parsert::parse_header()
{
  std::string headername;
  std::list<std::string> values;
  headert header;

  while(!tokenizer.peek().is_body())
  {
    auto token = tokenizer.consume();

    if(token.is_headername())
    {
      if(!headername.empty())
      {
        header.emplace_back(headername, std::move(values));
        values.clear();
      }

      if(token.is_headername())
        headername = token.text;
    }
    else if(token.is_string())
      values.push_back(token.string);
    else
      values.push_back(token.text);
  }

  if(!headername.empty())
    header.emplace_back(headername, std::move(values));

  return header;
}

hoat::bodyt hoa_parsert::parse_body()
{
  if(!tokenizer.consume().is_body())
    throw ebmc_errort() << "HOA-parser expected --BODY--";

  bodyt body;

  while(!tokenizer.peek().is_end())
  {
    auto state_name = parse_state_name();
    auto edges = parse_edges();
    body.emplace_back(std::move(state_name), std::move(edges));
  }

  return body;
}

hoat::state_namet hoa_parsert::parse_state_name()
{
  if(!tokenizer.consume().is_state())
    throw ebmc_errort() << "HOA-parser expected State:";

  state_namet state_name;

  // label?
  if(tokenizer.peek().text == "[")
    state_name.label = parse_label();

  // INT
  state_name.number = parse_int();

  // STRING?
  if(tokenizer.peek().is_string())
  {
    tokenizer.consume();
  }

  // acc-sig?
  if(tokenizer.peek().text == "{")
    state_name.acc_sig = parse_acc_sig();

  return state_name;
}

hoat::edgest hoa_parsert::parse_edges()
{
  edgest edges;

  while(!tokenizer.peek().is_end() && !tokenizer.peek().is_state())
  {
    auto edge = parse_edge();
    edges.push_back(std::move(edge));
  }

  return edges;
}

#include <iostream>

hoat::edget hoa_parsert::parse_edge()
{
  edget edge;

  // label?
  if(tokenizer.peek().text == "[")
    edge.label = parse_label();

  // state-conj: INT | state-conj "&" INT
  edge.dest_states.push_back(parse_int());
  while(tokenizer.peek().text == "&")
  {
    tokenizer.consume();
    edge.dest_states.push_back(parse_int());
  }

  // acc-sig?
  if(tokenizer.peek().text == "{")
    edge.acc_sig = parse_acc_sig();

  return edge;
}

hoat::acc_sigt hoa_parsert::parse_acc_sig()
{
  if(tokenizer.consume().text != "{")
    throw ebmc_errort() << "HOA-parser expected {";

  acc_sigt acc_sig;

  while(tokenizer.peek().text != "}")
  {
    auto token = tokenizer.consume();
    acc_sig.push_back(token.text);
  }

  tokenizer.consume();

  return acc_sig;
}

hoat::labelt hoa_parsert::parse_label()
{
  if(tokenizer.consume().text != "[")
    throw ebmc_errort() << "HOA-parser expected [";

  auto label = parse_label_expr();

  if(tokenizer.consume().text != "]")
    throw ebmc_errort() << "HOA-parser expected ]";

  return label;
}

hoat::labelt hoa_parsert::parse_label_expr_or()
{
  // label-expr ::= label-expr "|" label-expr
  auto irep = parse_label_expr_and();

  while(tokenizer.peek().text == "|")
  {
    tokenizer.consume();
    auto rhs = parse_label_expr_and();
    irep = irept{"|", {}, {std::move(irep), std::move(rhs)}};
  }

  return irep;
}

hoat::labelt hoa_parsert::parse_label_expr_and()
{
  // label-expr ::= label-expr "&" label-expr
  auto irep = parse_label_expr_primary();

  while(tokenizer.peek().text == "&")
  {
    tokenizer.consume();
    auto rhs = parse_label_expr_primary();
    irep = irept{"&", {}, {std::move(irep), std::move(rhs)}};
  }

  return irep;
}

hoat::labelt hoa_parsert::parse_label_expr_primary()
{
  // label-expr ::= BOOLEAN | INT | ANAME | "!" label-expr
  //                | "(" label-expr ")"
  auto token = tokenizer.consume();

  if(token.text == "!")
  {
    auto op = parse_label_expr_primary();
    return irept{"!", {}, {std::move(op)}};
  }
  else if(token.text == "(")
  {
    auto expr = parse_label_expr();
    if(tokenizer.consume().text != ")")
      throw ebmc_errort() << "HOA-parser expected )";
    return expr;
  }
  else
    return irept{token.text};
}

static void output(std::ostream &out, const hoat::acc_sigt &acc_sig)
{
  if(!acc_sig.empty())
  {
    out << " {";
    bool first = true;
    for(auto &acc_set : acc_sig)
    {
      if(first)
        first = false;
      else
        out << ' ';
      out << acc_set;
    }
    out << '}';
  }
}

static void output(std::ostream &out, const hoat::labelt &label)
{
  if(label.id() == "|")
  {
    DATA_INVARIANT(label.get_sub().size() == 2, "| must have two operands");
    auto &lhs = label.get_sub()[0];
    auto &rhs = label.get_sub()[1];
    output(out, lhs);
    out << label.id();
    output(out, rhs);
  }
  else if(label.id() == "&")
  {
    DATA_INVARIANT(label.get_sub().size() == 2, "& must have two operands");
    auto &lhs = label.get_sub()[0];
    auto &rhs = label.get_sub()[1];
    if(lhs.id() == "|")
      out << '(';
    output(out, lhs);
    if(lhs.id() == "|")
      out << ')';
    if(rhs.id() == "|")
      out << '(';
    out << label.id();
    output(out, rhs);
    if(rhs.id() == "|")
      out << ')';
  }
  else if(label.id() == "!")
  {
    DATA_INVARIANT(label.get_sub().size() == 1, "! must have one operand");
    auto &op = label.get_sub()[0];
    if(op.id() == "|" || op.id() == "&")
      out << '(';
    out << label.id();
    if(op.id() == "|" || op.id() == "&")
      out << ')';
    output(out, op);
  }
  else
  {
    out << label.id();
  }
}

void hoat::output(std::ostream &out) const
{
  for(auto &header_item : header)
  {
    out << header_item.first;
    for(auto &value : header_item.second)
      out << ' ' << value;
    out << '\n';
  }

  out << "--BODY--\n";

  for(auto &state : body)
  {
    out << "State:";
    if(!state.first.label.id().empty())
    {
      out << " [";
      ::output(out, state.first.label);
      out << ']';
    }
    out << ' ' << state.first.number;
    ::output(out, state.first.acc_sig);
    out << '\n';

    for(auto &edge : state.second)
    {
      if(!edge.label.id().empty())
      {
        out << '[';
        ::output(out, edge.label);
        out << "] ";
      }
      bool first = true;
      for(auto &dest : edge.dest_states)
      {
        if(first)
          first = false;
        else
          out << " & ";
        out << dest;
      }
      ::output(out, edge.acc_sig);
      out << '\n';
    }
  }

  out << "--END--\n";
}

grapht<graph_nodet<hoat::graph_edget>> hoat::graph() const
{
  grapht<graph_nodet<hoat::graph_edget>> graph;

  graph.resize(numeric_cast_v<std::size_t>(max_state_number() + 1));

  for(auto &state : body)
  {
    for(auto &edge : state.second)
      for(auto &dest : edge.dest_states)
      {
        graph.add_edge(state.first.number, dest);
        graph.edge(state.first.number, dest).label = edge.label;
      }
  }

  return graph;
}

void hoat::buechi_acceptance_cleanup()
{
  using hoa_grapht = grapht<graph_nodet<hoat::graph_edget>>;
  auto as_graph = graph();
  for(auto &state : body)
  {
    if(state.first.is_accepting())
    {
      hoa_grapht::patht loop_path;
      as_graph.shortest_loop(state.first.number, loop_path);
      // when this state is not part of any cycle,
      // then we cannot have Buechi acceptance via this state
      if(loop_path.empty())
        state.first.acc_sig.clear();
    }
  }
}
