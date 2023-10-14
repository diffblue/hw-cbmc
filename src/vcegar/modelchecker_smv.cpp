/*******************************************************************\

Module: SMV Model Checker Interface

Author: Daniel Kroening, Himanshu Jain

Date: June 2003

\*******************************************************************/

#include <cassert>
#include <cstdlib>
#include <ctype.h>
#include <fstream>
#include <list>
#include <algorithm>
#include <vector>
#include <sstream> 

#include <smvlang/expr2smv.h>

#include "modelchecker_smv.h"

/*******************************************************************\

Function: modelchecker_smvt::read_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelchecker_smvt::read_result
 (std::istream &out1,
  std::istream &out2,
  std::istream &out_ce,
  const abstract_transt &abstract_trans,
  abstract_counterexamplet &counterexample)
 {
  // check for errors first

   {
    std::list<std::string> file;

    while(true)
     {
      std::string line;
      if(!std::getline(out2, line)) break;
      file.push_back(line);
     }

    if(!file.empty())
      warning() << "NuSMV error see vcegar_tmp_smv_out2" << eom;
   }

  // now read output
   if(engine==CADENCE_SMV)
     return read_result_cadence_smv
       (out_ce,
	abstract_trans,
	counterexample);
   

   {
    std::list<std::string> file;

    while(true)
     {
      std::string line;
      if(!std::getline(out1, line)) break;
      file.push_back(line);
     }

    for(std::list<std::string>::const_iterator 
        it=file.begin(); it!=file.end(); it++)
     {
       std::string cex_text;
       unsigned length;

       //       #ifndef INVARSPEC
       cex_text = "-- specification";
       length = 16;
//        #else
//        cex_text = "-- invariant";
//        length = 12;
//        #endif
     
      if(std::string(*it, 0, length)==cex_text)
	{
        if(std::string(*it, it->size()-7)=="is true")
         {
          // OK
         }
        else if(std::string(*it, it->size()-8)=="is false")
         {
          // produce counterexample
          status() << "NuSMV produced counterexample" << eom;
	  read_counterexample(file, it, abstract_trans,
			      counterexample);
          status() << "NuSMV counterexample sucessfully read" << eom;

          // show it
          if (verbose) std::cout << counterexample;
          return false;
         }
        else
          throw "unexpected reply from NuSMV: \""+*it+"\"";
       }
     }
   }

  return true;
 }


/*******************************************************************\

Function: modelchecker_smvt::read_result_cadence_smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelchecker_smvt::read_result_cadence_smv(
  std::istream &out_ce,
  const abstract_transt &abstract_trans,
  abstract_counterexamplet &counterexample)
{
  std::list<std::string> file;

  while(true)
  {
    std::string line;
    if(!std::getline(out_ce, line)) break;
    file.push_back(line);
  }
  
  if(file.empty())
    throw "SMV error";

  for(std::list<std::string>::const_iterator 
      it=file.begin(); it!=file.end(); it++)
  {
    if(std::string(*it, 0, 18)=="/* truth value */ ")
    {
      if(std::string(*it, it->size()-1)=="1")
      {
        // OK
      }
      else if(std::string(*it, it->size()-1)=="0")
      {
        // produce counterexample
        status() << "Cadence SMV produced counterexample" << eom;
	
        read_counterexample_cadence_smv(
          file, it, abstract_trans,
          counterexample);


        debug() << "Cadence SMV counterexample sucessfully read" << eom;

        return false;
      }
      else
        throw "unexpected reply from Cadence SMV: \""+*it+"\"";
    }
  }

  return true;
}


/*******************************************************************\

Function: modelchecker_smvt::read_counterexample_cadence_smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::read_counterexample_cadence_smv(
  const std::list<std::string> &file,
  std::list<std::string>::const_iterator it,
  const abstract_transt &abstract_trans,
  abstract_counterexamplet &counterexample)
{
  while(it!=file.end() && *it!="{")
    it++;

  if(it==file.end())
    throw "unexpected end of counterexample";

  it++;

  //dummy
  std::vector<smv_ce_thread_infot> thread_infos;

  for(; it!=file.end(); it++)
  {
    if(*it=="}")
      break; // done with the trace

    if(std::string(*it, 0, 8)!="/* state")
      throw "expected state in counterexample, but got "+*it;
      
    abstract_statet abstract_state;
    abstract_state.predicate_values.
      resize(abstract_trans.variables.size());

    it++;
    if(it==file.end())
      throw "unexpected end of counterexample";

    for(; it!=file.end(); it++)
    {
      if(std::string(*it, 0, 1)=="#")
      {
        // ignore
      }
      else if(*it=="}")
      {
        // done with the state
        read_counterexample_store(
          counterexample, thread_infos, abstract_state);
        break;
      }
      else
      {
        std::string::size_type p=it->find('=');

        if(p==std::string::npos)
          throw "unexpected line in counterexample: "+*it;

        std::string original_variable(*it, 0, p-1);
        std::string value(*it, p+2, std::string::npos);

        while(!original_variable.empty() &&
              original_variable[0]==' ')
          original_variable.erase(0, 1);

        while(!original_variable.empty() &&
              original_variable[original_variable.size()-1]==' ')
          original_variable.erase(original_variable.size()-1, std::string::npos);

        std::string variable=original_variable;

        if(!variable.empty() && variable[0]=='\\')
          variable.erase(0, 1);

	//        unsigned thread_nr=0;

        if(variable.empty())
          throw "failed to get variable name";
        else if(variable[0]=='t') // checked for emptyness above
        {
	  throw "variable name starting with letter t ?. Not sure what it means \n";
        }

        if(variable=="PC")
	  {
	    throw "Found a variable named PC in the counterexample. Not sure what it means \n";
	  }
        else if(variable=="runs")
	  {
	    throw "Found a variable named runs in counterexample. Not sure what it means \n";
	  }
        else if(variable[0]=='b')
        {
          unsigned nr=atoi(variable.c_str()+1);
          if(nr>=abstract_state.predicate_values.size())
            throw "invalid variable in abstract counterexample: "+
              variable;

          abstract_state.predicate_values[nr]=atoi(value.c_str());
        }
        else
          throw "unknown variable in abstract counterexample: "+
	    original_variable+" (stripped: "+variable+")";
      }
    }
  }
  
  //std::cout << counterexample << std::endl;
}



/*******************************************************************\

Function: modelchecker_smvt::read_counterexample_store

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::read_counterexample_store
 (abstract_counterexamplet &counterexample,
  thread_infost &thread_infos,
  abstract_statet abstract_state)
{
  counterexample.push_back(abstract_state);
}

/*******************************************************************\

Function: modelchecker_smvt::read_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::read_counterexample
 (const std::list<std::string> &file,
  std::list<std::string>::const_iterator it,
  const abstract_transt &abstract_trans,
  abstract_counterexamplet &counterexample)
 {
  while(it!=file.end() && 
        (std::string(*it, 0, 1)=="*" ||
        (std::string(*it, 0, 1)=="-")))
    it++;

  abstract_statet abstract_state;
  abstract_state.predicate_values.resize(
    abstract_trans.variables.size());

  bool data_set=false;

  //dummy
  std::vector<smv_ce_thread_infot> thread_infos;

  for(; it!=file.end(); it++)
   {
     if (verbose) std::cout << "Xx " << *it << "\n";

    if(std::string(*it, 0, 3)=="-- ")
      break;
    else if(*it=="resources used:")
      break;
    else if(std::string(*it, 0, 6)=="state " ||
            std::string(*it, 0, 9)=="-> State " ||
            *it=="")
     {
      if(!data_set) continue;

      read_counterexample_store(
        counterexample, thread_infos, abstract_state);

      data_set=false;
     }
    else
     {
      std::string::size_type p=it->find('=');

      if(p==std::string::npos)
        throw "unexpected line in counterexample: "+*it;

      std::string original_variable(*it, 0, p-1);
      std::string value(*it, p+2, std::string::npos);

      while(!original_variable.empty() &&
            original_variable[0]==' ')
        original_variable.erase(0, 1);

      std::string variable=original_variable;

      unsigned thread_nr=0;

      if(variable.empty())
        throw "failed to get variable name";
      else if(variable[0]=='t') // checked for emptyness above
       {
        thread_nr=atoi(variable.c_str()+1);

        std::string::size_type q=original_variable.find('.');

        if(q==std::string::npos)
          throw "unexpected line in counterexample: "+*it;

        variable=std::string(original_variable, q+1, std::string::npos);

        if(variable.empty())
          throw "failed to get sub-variable name from "+original_variable;
       }

      if(variable=="PC")
       {
	 if (verbose) std::cout <<"Found a PC in counterexample \n";
        thread_infos[thread_nr].PC=atoi(value.c_str());
        data_set=true;
       }
      else if(variable=="runs")
       {
	 if (verbose) std::cout <<"Found runs in counterexample \n";
        thread_infos[thread_nr].runs=atoi(value.c_str());
        data_set=true;
       }
      else if(variable[0]=='b') // checked for emptyness above
       {
        unsigned nr=atoi(variable.c_str()+1);
        if(nr>=abstract_state.predicate_values.size())
          throw "invalid variable in abstract counterexample: "+
            variable;

        abstract_state.predicate_values[nr]=atoi(value.c_str());
        data_set=true;
       }
      else if(std::string(variable, 0, 5)=="guard")
       {
	 if (verbose) std::cout <<"Found a guard in counterexample \n";


       }
      else if(std::string(variable, 0, 6)=="event_")
       {
       }
      else if(std::string(variable, 0, 7)=="sticky_")
       {
       }
      else if(std::string(variable, 0, 6)=="nondet")
       {
       }
      else
        throw "unknown variable in abstract counterexample: "+
              original_variable+" (stripped: "+variable+")";
     }
   }

  if(data_set)
    read_counterexample_store(
      counterexample, thread_infos, abstract_state);
 }


/*******************************************************************\

Function: modelchecker_smvt::is_variable_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelchecker_smvt::is_variable_name(const std::string &name)
 {
  if(name=="") return false;

  for(unsigned i=0; i<name.size(); i++)
    if(!isalnum(name[i]) &&
       name[i]!='_')
      return false;

  return true;
 }

/*******************************************************************\

Function: modelchecker_smvt::get_variable_names

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::get_variable_names
 (const abstract_transt &abstract_trans)
 {

  variable_names.resize(abstract_trans.variables.size());

  for(unsigned i=0;
      i<abstract_trans.variables.size();
      i++)
   {
    variable_names[i]="b"+i2string(i);

    const std::string &description=
      abstract_trans.variables[i].description;


    if(is_variable_name(description))
      variable_names[i]+="_"+description;
   }
 }

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_global_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_global_variables
 (const abstract_transt &abstract_trans,
  std::ostream &out)
 {
  //
  // Program variables
  //

  out << "-- variables of the abstract program\n"
         "\n";

  unsigned max_len=0;

  for(unsigned i=0;
      i<abstract_trans.variables.size();
      i++)
    max_len=std::max(max_len, unsigned(variable_names[i].size()));

  for(unsigned i=0;
      i<abstract_trans.variables.size();
      i++)
   {
    out << "VAR " << variable_names[i]
        << ": boolean;";

    if(abstract_trans.variables[i].description!="")
     {
      for(unsigned j=0; j<(max_len+1-variable_names[i].size()); j++)
        out << " ";

      out << "-- " << abstract_trans.variables[i].description;
     }

    out << std::endl;
   }


  switch(engine)
    {
      //cadence smv projects some variables if they are not relevant, this produces wrong counterexample
      //following hack is a way to make sure cadence smv does not throw away initial state variables
    case CADENCE_SMV:
      out << "-- Hack for Cadence SMV \n";
      for(unsigned i=0; i<abstract_trans.variables.size(); i++)
	{
	  out << "TRANS (" << variable_names[i]
	      << " | !" << variable_names[i] <<")\n";
	}
      break;
    default:
      break;
    }

  out << std::endl;

 }



/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_cluster

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_trans_cluster
 (const abstract_transt &abstract_trans,
  const abstract_transition_relationt &cluster_trans,
  unsigned cluster_no,
  bool threaded,
  std::ostream &out)
 {
  //
  // Generate TRANS for the cubes
  //

   out << "-- the transition constraints for cluster no. " << cluster_no<< "\n"
         "\n";

  
  std::vector<unsigned> input(cluster_trans.input_predicates);
  std::vector<unsigned> output(cluster_trans.output_predicates);


  for (std::vector<unsigned>::const_iterator it = input.begin();
       it !=  input.end(); it++) 
    assert((*it >= 0) && (*it < abstract_trans.variables.size()));

   for (std::vector<unsigned>::const_iterator it = output.begin();
	it !=  output.end(); it++) 
     assert((*it >= 0) && (*it < abstract_trans.variables.size()));
  
   
   if(!cluster_trans.cubes.empty())
     {
       out << "TRANS " ;
       
       bool first=true;
       
       for(cubest::star_mapt::const_iterator
            s_it=cluster_trans.cubes.star_map.begin();
	   s_it!=cluster_trans.cubes.star_map.end();
	   s_it++)
	 {
	   const cubest::bitvt &stars=s_it->first;
	  
          for(cubest::bitssett::const_iterator
		b_it=s_it->second.begin();
              b_it!=s_it->second.end();
              b_it++)
	    {
	      const cubest::bitvt &bits=*b_it;

	      if(first)
		first=false;
	      else
		out << "              | ";
	      
            out << "(";

            unsigned bit=0;
            bool first_and=true;


	    
            assert(stars.size()==input.size()+output.size());

            for(unsigned i=0; i<input.size(); i++)
             {
              if(!stars[i])
               {
                assert(bit<bits.size());

                if(first_and)
                  first_and=false;
                else
                  out << " & ";

                if(!bits[bit])
                  out << "!";

                out << variable_names[input[i]];
               
                bit++;
               }
             }

            for(unsigned i=0; i<output.size(); i++)
             {
              if(!stars[i+input.size()])
               {
                assert(bit<bits.size());

                if(first_and)
                  first_and=false;
                else
                  out << " & ";

                if(!bits[bit])
                  out << "!";

                out << "next(" << variable_names[output[i]] << ")";
               
                bit++;
               }
             }

            if(bit==0) out << "1";

            out << ")" << std::endl;
           }
	}
      
      if(first) out << "1" << std::endl;
     }
   
   out << std::endl;
 }



/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_init_cluster

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_init_cluster
(const abstract_transt &abstract_trans,
 const abstract_initial_statest &initial_states,
 unsigned cluster_no,
 std::ostream &out)
{

  out << "-- Initial states cluster no. "<<cluster_no<< "\n \n";

  if(!initial_states.input_predicates.empty())
    {
      out << "INIT ";
      
      std::vector<unsigned> input(initial_states.input_predicates);
      
      for (std::vector<unsigned>::const_iterator it = initial_states.input_predicates.begin();
	   it !=  initial_states.input_predicates.end(); it++) 
	assert((*it >= 0) && (*it < abstract_trans.variables.size()));
      
      bool first=true;

      for(cubest::star_mapt::const_iterator
	    s_it=initial_states.cubes.star_map.begin();
	  s_it!=initial_states.cubes.star_map.end();
	  s_it++)
	{
	  const cubest::bitvt &stars=s_it->first;

	  for(cubest::bitssett::const_iterator
		b_it=s_it->second.begin();
	      b_it!=s_it->second.end();
	      b_it++)
	    {
	      const cubest::bitvt &bits=*b_it;

	      if(first)
		first=false;
	      else
		out << "            | ";

	      if(bits.size()==0) // empty clause?
		out << "1";
	      else
		{
		  out << "(";

		  unsigned bit=0;
		  bool first_and=true;

		  assert(stars.size()==input.size());

		  for(unsigned i=0; i<input.size(); i++)
		    {
		      if(!stars[i])
			{
			  assert(bit<bits.size());

			  if(first_and)
			    first_and=false;
			  else
			    out << " & ";

			  if(!bits[bit])
			    out << "!";

			  out << variable_names[input[i]];
             
			  bit++;
			}
		    }

		  out << ")" << std::endl;
		}
	    }
	}
    }
  
  out << std::endl;

}



/*******************************************************************\

Function: modelchecker_smvt::instantiate_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::instantiate_expression(exprt &expr)
 {
  Forall_operands(it, expr)
    instantiate_expression(*it);

  if(expr.id()=="predicate_symbol")
   {
    unsigned p=atoi(expr.get("identifier").c_str());
    expr.id("symbol");
    expr.set("identifier", variable_names[p]);
   }
  else if(expr.id()=="nondet_symbol")
   {
    nondet_symbolst::const_iterator it=
      nondet_symbols.find((exprt &)expr.find("expression"));

    if(it==nondet_symbols.end()) {
      std::cout <<expr <<"\n";
      throw "failed to find nondet_symbol";
    }

    typet type=expr.type();
    expr=exprt("symbol", type);
    expr.set("identifier", it->second);
   }
 }



/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_spec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_spec
 (const abstract_transt &abstract_trans,
  bool threaded,
  std::ostream &out)
 {
  //
  // Generate SPEC from assertions
  //

  out << "-- the specification\n"
         "\n";

  std::string prop_string;
  exprt tmp(abstract_trans.abstract_spec.property);
  instantiate_expression(tmp);
  expr2smv(tmp, prop_string);
  
  if (!claim)
    {
      out << "SPEC AG (" << prop_string << ") \n";

    }
  else
    {
      out << "SPEC " << prop_string << " \n";
    }
 }

/*******************************************************************\

Function: modelchecker_smvt::remove_spurious_transition

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::remove_spurious_transition
(const abstract_constraintt &start,
 const abstract_constraintt &final,
 std::ostream &out)
{
  out << "TRANS !(";

  print_constrain ( start, final, out);

  
  out << ")\n";
}


/*******************************************************************\

Function: modelchecker_smvt::remove_spurious_initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::remove_spurious_initial_state
(const abstract_constraintt &start,
 std::ostream &out)
{
  out << "INIT !("; 

  abstract_constraintt dummy;

  print_constrain ( start, dummy, out);

  out << ")\n";
}



/*******************************************************************\

Function: modelchecker_smvt::print_constrain

  Inputs:

 Outputs:

 Purpose: just prints a constrain

\*******************************************************************/

void modelchecker_smvt::print_constrain
(const abstract_constraintt &start,
 const abstract_constraintt &final,
 std::ostream &out)
{

  bool first = true;
  
  for(unsigned i=0; i<start.size(); i++)
    {
      switch (start[i]) { 
      case ZERO : {
	if (first) {
	  out << " !b" << i <<" ";
	  first = false;
	}
	else
	  out << "& !b" << i <<" ";
	break;
      }
      case ONE: {
	if (first) {
	  out << " b" << i <<" ";
	  first = false;
	}
	else
	  out << "& b" << i <<" ";
	
	break;
      }
      case NON_DET:
	//out << " b" << i << "= *"   <<" ";
	break;
      }
    }

  for(unsigned i=0; i<final.size(); i++)
    {
      switch (final[i]) { 
      case ZERO : {
	if (first) {
	  out << " !next(b" << i <<") ";
	  first = false;
	}
	else
	  out << "& !next(b" << i <<") ";
	break;
      }
      case ONE: {
	if (first) {
	  out << " next(b" << i <<") ";
	  first = false;
	}
	else
	  out << "& next(b" << i <<") ";
	
	break;
      }
      case NON_DET:
	break;
      }
    }
  
  if (first)
    out << " 1 ";
  
}


/*******************************************************************\

Function: modelchecker_smvt::print_constrain

  Inputs:

 Outputs:

 Purpose: just prints a constrain

\*******************************************************************/

void modelchecker_smvt::add_weakest_precondition_constrain
(const abstract_constraintt &start1,
 const abstract_constraintt &final1,
 const abstract_constraintt &start2,
 const abstract_constraintt &final2,
 std::ostream &out)
{
  //identify the differing predicate in start1 and start2

  abstract_constraintt start3, dummy_final3;

  int count = 0;


  if (start1.size() == start2.size())
    {
      for (unsigned i = 0 ; i < start1.size(); i++) {
	if (start1[i] != start2[i]) {
	  start3.push_back(NON_DET);
	  count ++;
	}
	else
	  start3.push_back(start1[i]);
      }
      assert (count == 1); //basically start1 and start2 should differ at only one position
    }
  else
    {
      assert((start1.empty() && final1.empty() ) ||
	     (start2.empty() && final2.empty() ));
      start3 = start1.empty()?start2:start1; 
    }

  out << "TRANS (";

  if (!start1.empty())
    print_constrain (start1, final1, out);
  else
    {
      assert(final1.empty());
      out << " 0 ";
    }

  out << ") \n | (";
  
  if (!start2.empty())
    print_constrain (start2, final2, out);
  else
    {
      assert(final2.empty());
      out << " 0 ";
    }

  out << ") \n | !(";

  print_constrain (start3, dummy_final3, out);

  out << ") \n";

}





/*******************************************************************\

Function: modelchecker_smvt::build_smv_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file
(const abstract_transt &abstract_trans,  
 const abstract_transition_constrainst &abstract_transition_constrains,
 const weakest_precondition_constrainst &weakest_precondition_constrains, 
 const abstract_initial_constrainst &abstract_initial_constrains,
 bool threaded,
 std::ostream &out)
{
  unsigned i=0;

  //Add initial states constraints.
  
  for(std::vector<abstract_initial_statest>::const_iterator it =
	abstract_trans.abstract_init_vector.begin(); 
      it!=abstract_trans.abstract_init_vector.end(); it++) {
    
    build_smv_file_init_cluster(abstract_trans, *it, i, out);
    i++;
  }

  out << "-- removal of spurious initial states \n"
    "\n";
  
  for( abstract_initial_constrainst::const_iterator it = 
	 abstract_initial_constrains.begin();
       it !=  abstract_initial_constrains.end() ; it++)
    remove_spurious_initial_state(*it, out);
  
 

  i=0;

  //Add transition relation for each cluster.

  for(std::vector<abstract_transition_relationt>::const_iterator it =
      abstract_trans.abstract_trans_vector.begin(); 
      it!=abstract_trans.abstract_trans_vector.end(); it++) {
   
    build_smv_file_trans_cluster(abstract_trans, *it, i, threaded, out);
    i++;
  }


  out << "-- transition relation for predicates generated from refinement\n"
    "\n";

  for(std::vector<abstract_transition_relationt>::const_iterator it =
      abstract_trans.refinement_preds_trans_vector.begin(); 
      it!=abstract_trans.refinement_preds_trans_vector.end(); it++) {
   
    build_smv_file_trans_cluster(abstract_trans, *it, i, threaded, out);
    i++;
  }


  i = 0;
  
  //Remove abstract spurious transitions.
  out << "-- removal of spurious transitions\n"
    "\n";
  
  
  for( abstract_transition_constrainst::const_iterator it = 
	 abstract_transition_constrains.begin();
       it !=  abstract_transition_constrains.end() ; it++)
    {
      remove_spurious_transition(it->first, it->second, out);
    }

  out << "-- addition of weakest pre-condition constraints \n"
    "\n";
  
  
  for( weakest_precondition_constrainst::const_iterator it = 
	 weakest_precondition_constrains.begin();
       it !=  weakest_precondition_constrains.end() ; it++)
    {
      add_weakest_precondition_constrain((it->first).first, (it->first).second, 
					 (it->second).first, (it->second).second, out);
    }
  

  build_smv_file_spec(abstract_trans, threaded, out);
  
}


/*******************************************************************\

Function: modelchecker_smvt::build_smv_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file
(const abstract_transt &abstract_trans,
 const abstract_transition_constrainst &abstract_transition_constrains,
 const weakest_precondition_constrainst &weakest_precondition_constrains, 
 const abstract_initial_constrainst &abstract_initial_constrains,
 std::ostream &out)
{
  // start printing NuSMV

  out << "-- automatically generated by VCEGAR\n"
    "\n";

  out << "MODULE main\n"
	"\n";
  
  build_smv_file_global_variables(abstract_trans, out);
  
  build_smv_file(abstract_trans, abstract_transition_constrains,  
		 weakest_precondition_constrains, abstract_initial_constrains, false, out);
}

/*******************************************************************\

Function: modelchecker_smvt::check

  Inputs:

 Outputs:

 Purpose: model check an abstract program using SMV, return
          counterexample if failed
          Return value of TRUE means the program is correct,
          if FALSE is returned, ce will contain the counterexample

 weakest pre-condition relationships between predicates  
 basically spurious transitions 
\*******************************************************************/

bool modelchecker_smvt::check
(const abstract_transt &abstract_trans,
 const abstract_transition_constrainst &abstract_transition_constrains, 
 const weakest_precondition_constrainst &weakest_precondition_constrains, 
 const abstract_initial_constrainst &abstract_initial_constrains,
 abstract_counterexamplet &counterexample)
{
  get_variable_names(abstract_trans);


  std::string temp_base="vcegar_tmp";

  std::string temp_smv=temp_base+"_abstract.smv";
  std::string temp_smv_out1=temp_base+"_smv_out1";
  std::string temp_smv_out2=temp_base+"_smv_out2";
  std::string temp_smv_out_ce=temp_base+"_abstract.out";
  
  remove(temp_smv_out1.c_str());
  remove(temp_smv_out2.c_str());
  remove(temp_smv_out_ce.c_str());


  {
      std::ofstream out(widen_if_needed(temp_smv));
      build_smv_file(
        abstract_trans,
        abstract_transition_constrains,
        weakest_precondition_constrains,
        abstract_initial_constrains,
        out);
  }

  {
    std::string command;
    
    switch(engine)
      {
      case NUSMV:
	command="NuSMV -f ";
	status() << "Running NuSMV: " << command << eom;
	break;

      case  CMU_SMV:
	status() << "Running CMU SMV: " << command << eom;
	command="smv";
	break;

      case CADENCE_SMV:
	//-sift
	//	command="smv -force ";
	command="smv ";

	if (absref3)
	  command+=" -absref3 ";

	status() << "Running Cadence SMV: " << command << eom;
	break;

      default:
	assert(false);
      }
    
    command+=" "+temp_smv+" >"+temp_smv_out1+
      " 2>"+temp_smv_out2;

    system(command.c_str());
  }
  
  bool result;
  
  {
    std::ifstream out1(widen_if_needed(temp_smv_out1)),
      out2(widen_if_needed(temp_smv_out2)),
      out_ce(widen_if_needed(temp_smv_out_ce));

    result=read_result(out1, out2, out_ce, abstract_trans,
		       counterexample);
  }
  
  if (verbose)
  status() << "Length of the abstract counterexample is "
           << counterexample.size() << eom;

  int count;
  for (std::vector<abstract_statet>::const_iterator it =
	 counterexample.begin(); it != counterexample.end(); it++) {
    count =0;
    for (std::vector<bool>::const_iterator p_it =
	   (it->predicate_values).begin(); 
	 p_it != (it->predicate_values).end(); p_it++) {
      count++;
    }
  }
 
 
  return result;
}
