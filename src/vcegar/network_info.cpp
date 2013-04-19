/*******************************************************************\

Module: Creates network for a given circuit. 

Author: Himanshu Jain

\*******************************************************************/

#include <cassert>

#include <util/cout_message.h>
#include <util/simplify_expr.h>

#include <verilog/expr2verilog.h>

#include "network_info.h"
#include "instantiate_guards.h"

//#define DEBUG

/*******************************************************************\

Function: create

  Inputs:

 Outputs:

 Purpose: Fills the next state function cache and collect symbols
          which belong to a same network

\*******************************************************************/

void network_infot::create(
  const exprt &constraints,
  const exprt &trans,
  const var_mapt &var_map)
{
   exprt copy_constraints(constraints);
   namespacet ns(context);
   ns.follow_macros(copy_constraints);

   create_network(copy_constraints, 
		  vector_symbolsets, 
		  vector_exprsets, 
		  var_map);
   #ifdef DEBUG
   print_network(vector_symbolsets, 
		  vector_exprsets, 
		  var_map);

   std::cout <<"Now building the next state function cache \n";
   
   #endif

   exprt copy_trans(trans);
   ns.follow_macros(copy_trans);
 


   std::cout << "Build next state functions cache\n";
   build_next_state_function_cache(copy_trans,
				   vector_symbolsets, 
				   vector_exprsets,
				   var_map,
				   next_state_function_cache);

}

/*******************************************************************\

Function: lookup

  Inputs:

 Outputs:

 Purpose: Looks for an element in a vector of sets

\*******************************************************************/

bool network_infot::lookup(
  const std::vector<std::set<irep_idt> > &vector_symbolsets,
  const irep_idt &name,
  unsigned& nr) const
{
  for (unsigned i=0; i<vector_symbolsets.size(); i++)
  {
    std::set<irep_idt>::const_iterator it = 
      vector_symbolsets[i].find(name);
    
    if (it != vector_symbolsets[i].end()) {
      nr =i;
      return true;
    }
  }
  
  return false;
}


//This needs to be replaced by a union find data structure!!

/*******************************************************************\

Function: create_network

  Inputs:

 Outputs:

 Purpose: Creates sets of symbols which are equal to each other.

\*******************************************************************/

void network_infot::create_network (
  const exprt& general_constrains,
  std::vector<std::set<irep_idt> > &vector_symbolsets,
  std::vector<std::set<exprt> > &vector_exprsets,
  const var_mapt &var_map)
{
  if (!general_constrains.has_operands()) return;
  
  if(general_constrains.id()=="=")
    {
      
      if (!( (general_constrains.operands()[0]).id()=="symbol" ||
	     (general_constrains.operands()[1]).id()=="symbol"))
	return;

      

      unsigned pos0;
      unsigned pos1;

      irep_idt id0 = "", id1 = "";

      bool is_symbol0=false, is_symbol1=false;
      int var_type0=-1, var_type1=-1;
      
      if ((general_constrains.operands()[0]).id()==ID_symbol)
      {
	id0=(general_constrains.operands()[0]).get(ID_identifier);

	var_type0 = get_type_integer(var_map, id0);
	is_symbol0 = true;
      }
	
      if ((general_constrains.operands()[1]).id()==ID_symbol)
      {
	id1= (general_constrains.operands()[1]).get(ID_identifier);

	var_type1 = get_type_integer(var_map, id1);
	is_symbol1 = true;
      }

      assert(is_symbol0 || is_symbol1);
      assert(!(var_type0 ==4 || var_type1==4));

      if (!lookup(vector_symbolsets, id0, pos0))
      {
	if (!lookup(vector_symbolsets, id1, pos1))
	{
	  std::set<irep_idt> new_set;

	  if (is_symbol0)
	    new_set.insert(id0);

	  if (is_symbol1)
	    new_set.insert(id1);
	  
	  vector_symbolsets.push_back(new_set);
	  
	  std::set<exprt> new_expr_set;
	  exprt copy0(general_constrains.operands()[0]);
	  exprt copy1(general_constrains.operands()[1]);

	  if (var_type0 == 1 || !is_symbol0) //latch or macro definition
	    new_expr_set.insert(copy0);
	  
	  if (var_type1 == 1 || !is_symbol1) //latch or macro definition
	    new_expr_set.insert(copy1);

	  vector_exprsets.push_back(new_expr_set);

	}
	else {
	  if (is_symbol0)
	    vector_symbolsets[pos1].insert(id0);

	  exprt copy(general_constrains.operands()[0]);
	  if (var_type0 == 1 || !is_symbol0)
	    vector_exprsets[pos1].insert(copy);
	}
      }
      else {

	if (!lookup(vector_symbolsets, id1, pos1))
	  {
	    if (is_symbol1)
	      vector_symbolsets[pos0].insert(id1);
	    
	    exprt copy(general_constrains.operands()[1]);
	    
	    if (var_type1 == 1 || !is_symbol1)
	      vector_exprsets[pos0].insert(copy);
	  }
	else
	  {
	    if (pos1 < pos0)
	      {
		unsigned tmp = pos1;
		pos1 = pos0;
		pos0 = tmp;
	      }

	    vector_symbolsets[pos0].insert(vector_symbolsets[pos1].begin(),
					   vector_symbolsets[pos1].end());
	    vector_symbolsets[pos1].clear();

	    vector_exprsets[pos0].insert(vector_exprsets[pos1].begin(),
					 vector_exprsets[pos1].end());
	    vector_exprsets[pos1].clear();
	  }
      }
      return;
    }
  
  if(general_constrains.has_operands())
    forall_operands(it, general_constrains)
      create_network(*it, vector_symbolsets, vector_exprsets, var_map);
  
}


/*******************************************************************\

Function: print_network

  Inputs:

 Outputs:

 Purpose: Prints the set of symbols in the network

\*******************************************************************/

void network_infot::print_network(
  const std::vector<std::set<irep_idt> > &vector_symbolsets,
  const std::vector<std::set<exprt> > &vector_exprsets,
  const var_mapt &var_map) 
{
  for (unsigned i=0; i<vector_symbolsets.size(); i++)
  {
    std::cout <<"Symbol set ["<< i<<"]\n";
    print_symbolset(vector_symbolsets[i], var_map);
    print_exprset(vector_exprsets[i]);
    std::cout <<"\n";
  }
}


/*******************************************************************\

Function: print_symbolset

  Inputs:

 Outputs:

 Purpose: Prints the set of symbols in the network

\*******************************************************************/

void network_infot::print_symbolset(
  const std::set<irep_idt> &symbolset,
  const var_mapt &var_map)
{
  for(std::set<irep_idt>::const_iterator
      it = symbolset.begin();
      it != symbolset.end();
      it++)
  {
    var_mapt::vart::vartypet var_type = var_map.get_type(*it);

    std::cout <<*it <<"  ";
    
    switch(var_type) 
      {
      case var_mapt::vart::VAR_LATCH:
	std::cout <<"LATCH";
	break;
      case var_mapt::vart::VAR_INPUT: 
	std::cout <<"INPUT";
	break;
      case var_mapt::vart::VAR_WIRE : 
	std::cout <<"WIRE";
	break;
	
      default: 
	std::cout <<"NOT FOUND ";
	break;
      }
    std::cout <<"\n"; 
  }
}



/*******************************************************************\

Function: print_exprset

  Inputs:

 Outputs:

 Purpose: Prints the set of symbols in the network

\*******************************************************************/

void network_infot::print_exprset (const std::set<exprt>  &exprset) {

  if (exprset.size() == 0) {
    std::cout <<"Exprset is empty \n";
    return;
  }

  unsigned count = 0;

  for (std::set<exprt>::const_iterator it = exprset.begin();
       it != exprset.end(); it++)
  {
    std::string code=expr2verilog(*it);
    std::cout << " [" << count << "] " << code << "\n";
    count ++;
  }
  
  if (exprset.size() > 1) 
    std::cout << "WARNING: Network has multiple definitions: \n";
}

/*******************************************************************\

Function: replace_outputs

  Inputs:

 Outputs:

 Purpose: Replaces (not external) inputs and wires with their definitions 
 in terms of latches and other expressions if any.
\*******************************************************************/

void network_infot::replace_outputs(
  exprt &property,
  const std::vector<std::set<irep_idt> > &vector_symbolsets,
  const std::vector<std::set<exprt> > &vector_exprsets,
  const var_mapt &var_map) const
{
  #ifdef DEBUG
  std::cout << "property is " << property << "\n";
  #endif

  if(property.has_operands())
    Forall_operands(it, property)
      replace_outputs(*it, vector_symbolsets, vector_exprsets, var_map);
  

  if(property.id()==ID_symbol)
  {
      irep_idt module_variable = property.get(ID_identifier);


      var_mapt::vart::vartypet var_type = var_map.get_type(module_variable);

      #ifdef DEBUG
      std::cout <<"module variable is "<<module_variable<<"\n";
      #endif

      switch(var_type) 
	{
	case var_mapt::vart::VAR_LATCH: 
	  { //Its a latch do nothing.
	    break;
	  }
	case var_mapt::vart::VAR_INPUT: //Input
	  {
	    unsigned pos0;
	    exprt def;
	    
	    if (lookup(vector_symbolsets, module_variable, pos0)) {
	      if (!vector_exprsets[pos0].empty()) {
		property = *(vector_exprsets[pos0].begin());
		replace_outputs(property, vector_symbolsets, vector_exprsets,  var_map);
	      }
	    }
	    break;
	  }
	case var_mapt::vart::VAR_WIRE : //wire
	  {
	    unsigned pos0;
	    exprt def;

	    if (lookup(vector_symbolsets, module_variable, pos0)) {
	      if (!vector_exprsets[pos0].empty()) {
		property = *(vector_exprsets[pos0].begin());
		replace_outputs(property, vector_symbolsets, vector_exprsets,  var_map);
	      }
	    }
	    break;
	  }

	default: 
	  {
	     std::cout <<"Warning !!" <<module_variable <<" is not defined in the internal variable map \n";
	     assert(0);
	     break;
	  }
	}
    }
}	  

/*******************************************************************\

Function: build_next_state_function_cache

  Inputs:

 Outputs:

 Purpose: Creates the next state function cache and also performs 
          replace outputs on the stored function. 
\*******************************************************************/

void network_infot::build_next_state_function_cache(
  const exprt &trans_rel, 
  const std::vector<std::set<irep_idt> > &vector_symbolsets,
  const std::vector<std::set<exprt> > &vector_exprsets,
  const var_mapt &var_map,
  next_state_function_cachet &next_state_function_cache)
{
  
  if (!trans_rel.has_operands()) return;

  if(trans_rel.id()=="=")
    {

      exprt t1= (trans_rel.operands())[0];
      exprt t2= (trans_rel.operands())[1];
      
      if (t1.id()== "next_symbol") {

	#ifdef DEBUG
	std::cout <<"Found "<< t1.get("identifier")<<"\n";
	#endif

	exprt def(t2); 
	replace_outputs(def, 
			vector_symbolsets, 
			vector_exprsets,
			var_map);
	

	next_state_function_cache.insert(std::pair<irep_idt, exprt>
					 (t1.get(ID_identifier), def));
	
        return;
      }   
    }
  
  if(trans_rel.has_operands())
    forall_operands(it, trans_rel) {
      build_next_state_function_cache(*it, 
				      vector_symbolsets,
				      vector_exprsets,
				      var_map,
				      next_state_function_cache);
  
  }
}

/*******************************************************************\

Function: Print the cache of the next state functions

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void network_infot::print_next_state_function_cache
(const next_state_function_cachet &next_state_function_cache)
{
  unsigned count =0;
  for ( next_state_function_cachet::const_iterator it= next_state_function_cache.begin();
	it != next_state_function_cache.end();
	it++)
    {
      std::cout <<"[" << count <<" "<<it->first<<"]--\n";
      std::cout<<expr2verilog(it->second)<<"\n\n";
      count++;
    }
}



/*******************************************************************\

Function: print_members() ;

  Inputs:

 Outputs:

 Purpose: Public method

\*******************************************************************/

void network_infot::print_members() {
   print_network (vector_symbolsets, vector_exprsets, var_map);
}

/*******************************************************************\

Function: print_next_state_function_cache

  Inputs:

 Outputs:

 Purpose: Public method

\*******************************************************************/

void network_infot::print_next_state_function_cache() {
  print_next_state_function_cache (next_state_function_cache);
}


/*******************************************************************\

Function: weakest_precondition_recur

  Inputs:

 Outputs:

 Purpose: Computes the weakest precondition of a given property. Takes case splits
          into account.

\*******************************************************************/


void network_infot::weakest_precondition_recur (exprt& property) const
{
  if (property.id() == "with") {
    std::cout <<"Giving up accuracy here ! \n";
    return;
  }
  
  if(property.has_operands())
    Forall_operands(it, property)
      weakest_precondition_recur(*it);
  
  if(property.id()==ID_next_symbol)
    {
      const irep_idt &next_state_variable=property.get(ID_identifier);

      next_state_function_cachet::const_iterator pair = 
	next_state_function_cache.find(next_state_variable);
      
      if (pair != next_state_function_cache.end()) {
	property = pair->second;
      }
      else {
	property.id(ID_symbol); 
      }
    }
}

/*******************************************************************\

Function: weakest_precondition

  Inputs:

 Outputs:

 Purpose: Computes the weakest precondition of a given property. Takes case splits
          into account.

\*******************************************************************/

void network_infot::weakest_precondition (exprt& property) const
{
  rename (property);
  weakest_precondition_recur (property);
}
 
/*******************************************************************\

Function: Wrapper for the internal replace_outputs routine.

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/


void network_infot::replace_outputs (exprt& property) const
{
  replace_outputs(property, vector_symbolsets, vector_exprsets, var_map);
}



/*******************************************************************\

Function: weakest_precondition_recur

  Inputs:

 Outputs:

 Purpose: Computes the weakest precondition of a given property. Takes case splits
          into account. Use the next state function cache supplied by the user.

\*******************************************************************/


void network_infot::weakest_precondition_recur (exprt& property, const next_state_function_cachet &ns_cache) const
{
  if (property.id() == ID_with)
  {
    std::cout << "Giving up accuracy here!\n";
    return;
  }

  if(property.has_operands())
    Forall_operands(it, property)
      weakest_precondition_recur(*it, ns_cache);
   
  if(property.id()==ID_next_symbol)
    {

      const irep_idt &next_state_variable=property.get(ID_identifier);

      next_state_function_cachet::const_iterator pair = 
	ns_cache.find(next_state_variable);


      if (pair != ns_cache.end()) {
	property = pair->second;
      }
      else {
	#ifdef DEBUG
	const irep_idt &next_state_variable = property.get(ID_identifier);
	
	std::cout <<"Identifier "<<next_state_variable<<" has no next state function\n";
	#endif
	property.id(ID_symbol);
      }
    }
}

/*******************************************************************\

Function: simplified_weakest_precondition

  Inputs:

 Outputs:

 Purpose: Before substituting the next state functions. First try to
simplify them.

\*******************************************************************/

void network_infot::simplified_weakest_precondition(
  exprt &property, 
  const abstract_statet &abstract_state, 
  const predicatest &predicates,
  std::set<unsigned> &preds_used_to_simplify,
  bool &containsInput) const
{
  next_state_function_cachet simplified_ns_funcs;

  rename (property);

  weakest_precondition_recur_demand(
    abstract_state, predicates,
    property, simplified_ns_funcs, 
    preds_used_to_simplify,
    containsInput); 

  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);
  simplify(property, ns);

  instantiate_guards_simplify(predicates, abstract_state, 
			      property, preds_used_to_simplify);

  #ifdef DEBUG
  std::cout <<"The size of simplified cache is "<<simplified_ns_funcs.size()<<"\n";
  #endif

  simplified_ns_funcs.clear(); 
}


/*******************************************************************\

Function: weakest_precondition_recur_demand

  Inputs:

 Outputs:

 Purpose: Before substituting the next state functions. First try to
simplify them. But only simplify on demand.

Also collect the predicates which are useful for simplication. 
(useful for syntactic abstraction)

Date : Dec 24, 2004
\*******************************************************************/


void network_infot::weakest_precondition_recur_demand(
  const abstract_statet &abstract_state, 
  const predicatest &predicates,
  exprt& property, 
  next_state_function_cachet &ns_cache,
  std::set<unsigned> &preds_used_to_simplify,
  bool &containsInput) const 
{

  if(property.has_operands())
    Forall_operands(it, property)
      weakest_precondition_recur_demand(abstract_state, predicates, *it, 
					ns_cache, 
					preds_used_to_simplify,
					containsInput);
   
  if(property.id()=="next_symbol")
  {
    const irep_idt &next_state_variable = property.get(ID_identifier);

      next_state_function_cachet::const_iterator pair = 
	ns_cache.find(next_state_variable);
      
      
      if (pair != ns_cache.end()) {
	property = pair->second;
      }
      else {
	// Let us try to get the next state function, simplify it, and cache it.

	next_state_function_cachet::const_iterator it= 
	  next_state_function_cache.find(next_state_variable);

	if (it != next_state_function_cache.end()) {

	  exprt simplify_ns (it->second);

	  #ifdef DEBUG  
	  std::cout << "Before simplification \n";
	  std::cout <<"[" <<it->first<<"]--\n";
	  std::cout <<simplify_ns << "\n";
	  #endif



	  instantiate_guards_simplify (predicates, abstract_state, 
				       simplify_ns, preds_used_to_simplify);



	  #ifdef DEBUG  
	  std::cout << "After simplification \n";
	  std::cout <<"[" <<it->first<<"]--\n";
	  //  std::cout<<simplify_ns<<"\n\n";
	  std::cout<<expr2verilog(simplify_ns)<<"\n\n";
	  #endif

	  //update the property
	  property = simplify_ns;
	  

	  //Insert simplified next state function in the cache.
	  ns_cache.insert(std::pair<irep_idt, exprt>
			  (it->first, simplify_ns));
	  
      

	}
	else {
	
	  property.id("symbol");
	  
	  containsInput = true;
	  
          #ifdef DEBUG
	  const dstring &next_state_variable = property.get("identifier");
	  std::cout <<"Identifier "<<next_state_variable<<" has no next state function\n";
          #endif
	}
      }
    }
}


