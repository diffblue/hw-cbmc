// A minimalistic BDD library, following Bryant's original paper
// and Andersen's lecture notes
//
// Written by Daniel Kroening on the 28th of September 2009

#ifndef miniBDD_H
#define miniBDD_H

#include <list>
#include <vector>
#include <map>
#include <string>

class BDD
{
public:
  inline BDD();
  inline BDD(const BDD &x);
  inline ~BDD();

  // Boolean operators on BDDs
  BDD operator !() const;
  BDD operator ^(const BDD &) const;
  BDD operator ==(const BDD &) const;
  BDD operator &(const BDD &) const;
  BDD operator |(const BDD &) const;
  
  // copy operator
  inline BDD &operator=(const BDD &);
  
  friend class miniBDD_mgr;
  friend BDD apply(bool (*fkt)(bool x, bool y), const BDD &x, const BDD &y);
  
  inline bool is_constant() const;
  inline bool is_true() const;
  inline bool is_false() const;

  inline unsigned var() const;
  inline const BDD &low() const;
  inline const BDD &high() const;
  inline unsigned node_number() const;
  
  void clear();
  
protected:
  explicit inline BDD(class BDDnode *_node);
  class BDDnode *node;
};

class BDDnode
{
public:
  class miniBDD_mgr *mgr;
  unsigned var, node_number, reference_counter;
  BDD low, high;
  
  inline BDDnode(
    class miniBDD_mgr *_mgr,
    unsigned _var, unsigned _node_number,
    const BDD &_low, const BDD &_high);

  inline void add_reference();
  void remove_reference();
};

class miniBDD_mgr
{
public:
  miniBDD_mgr();
  ~miniBDD_mgr();

  BDD Var(const std::string &label);

  void DumpDot(std::ostream &out, bool supress_zero=false) const;
  void DumpTikZ(std::ostream &out, bool supress_zero=false, bool node_numbers=true) const;
  void DumpTable(std::ostream &out) const;

  inline const BDD &True();
  inline const BDD &False();
  
  friend class BDD;
  friend class BDDnode;
  
protected:
  typedef std::list<BDDnode> nodest;
  nodest nodes;
  BDD true_bdd, false_bdd;
  
  struct var_table_entryt
  {
    std::string label;
    inline var_table_entryt(const std::string &_label);
  };  

  typedef std::vector<var_table_entryt> var_tablet;
  var_tablet var_table;  
  
  // this is our reverse-map for nodes
  struct reverse_keyt
  {
    unsigned var, low, high;
    inline reverse_keyt(
      unsigned _var, const BDD &_low, const BDD &_high);
  };
  
  typedef std::map<reverse_keyt, BDDnode *> reverse_mapt;
  reverse_mapt reverse_map;
  
  friend bool operator < (const reverse_keyt &x, const reverse_keyt &y);

  // create a node (consulting the reverse-map)
  BDD mk(unsigned var, const BDD &low, const BDD &high);

  friend BDD apply(bool (*fkt)(bool x, bool y), const BDD &x, const BDD &y);
};

BDD apply(bool (*fkt)(bool x, bool y), const BDD &x, const BDD &y);

#define forall_nodes(it) for(nodest::const_iterator it=nodes.begin(); \
  it!=nodes.end(); it++)

// inline functions
#include "miniBDD.inc"

#endif
