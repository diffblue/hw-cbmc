// inline functions

BDD::BDD():node(NULL)
{
}

BDD::BDD(const BDD &x):node(x.node)
{
  if(node!=NULL) node->add_reference();
}

BDD::BDD(BDDnode *_node):node(_node)
{
  if(node!=NULL) node->add_reference();
}

BDD &BDD::operator=(const BDD &x)
{
  assert(&x!=this);
  clear();

  node=x.node;

  if(node!=NULL) node->add_reference();

  return *this;
}

BDD::~BDD()
{
  clear();
}

bool BDD::is_constant() const
{
  assert(node!=NULL);
  return node->node_number<=1;
}

bool BDD::is_true() const
{
  assert(node!=NULL);
  return node->node_number==1;
}

bool BDD::is_false() const
{
  assert(node!=NULL);
  return node->node_number==0;
}

unsigned BDD::var() const
{
  assert(node!=NULL);
  return node->var;
}

unsigned BDD::node_number() const
{
  assert(node!=NULL);
  return node->node_number;
}

const BDD &BDD::low() const
{
  assert(node!=NULL);
  assert(node->node_number>=2);
  return node->low;
}

const BDD &BDD::high() const
{
  assert(node!=NULL);
  assert(node->node_number>=2);
  return node->high;
}

BDDnode::BDDnode(
  miniBDD_mgr *_mgr,
  unsigned _var, unsigned _node_number,
  const BDD &_low, const BDD &_high):
  mgr(_mgr), var(_var), node_number(_node_number),
  reference_counter(0),
  low(_low), high(_high)
{
}

miniBDD_mgr::var_table_entryt::var_table_entryt(
  const std::string &_label):label(_label)
{
}

const BDD &miniBDD_mgr::True()
{
  return true_bdd;
}

const BDD &miniBDD_mgr::False()
{
  return false_bdd;
}
  
void BDDnode::add_reference()
{
  reference_counter++;
}
  
miniBDD_mgr::reverse_keyt::reverse_keyt(
  unsigned _var, const BDD &_low, const BDD &_high):
  var(_var), low(_low.node->node_number), high(_high.node->node_number)
{
}
