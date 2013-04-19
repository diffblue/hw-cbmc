/*******************************************************************\

Module: Predicate Manager

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PREDICATES_H
#define CPROVER_PREDICATES_H

#include <set>

#include <util/expr.h>

typedef exprt predicatet;

class predicatest
 {
 public:
   typedef enum {INITIAL, FINAL, NOT_DEFINED} statet;

   predicatest(){}
   ~predicatest(){}

  // find (and add, if not found) a predicate
  unsigned lookup(const predicatet &predicate);

  //Same task as the above function except that the
  //the number for the predicate to be inserted is provided
  //by the user as the second argument.
  void lookup(const predicatet &predicate, 
	      unsigned predicate_num, 
	      statet state);
  
  // just find (and do not add, if not found) a predicate
  // true = predicate found
  bool find(const predicatet &predicate) const
   {
    return predicate_map.find(predicate)!=predicate_map.end();
   }
  
  // just find (and do not add, if not found) a predicate
  // true = predicate found
  bool find(const predicatet &predicate, unsigned &nr) const
   {
    predicate_mapt::const_iterator it=
      predicate_map.find(predicate);
      
    if(it==predicate_map.end())
      return false;
      
    nr=it->second;
    
    return true;
   }
  
  const predicatet &operator[](unsigned nr) const
   {
    return predicate_vector[nr]->first;
   }

  

  statet get_state(const predicatet &predicate) const
    {
      predicate_statet::const_iterator it=
	predicate_state.find(predicate);

      if (it==predicate_state.end())
	return NOT_DEFINED;
      else
	return it->second; 
    }


  bool get_info(const predicatet &predicate, 
		unsigned& nr, statet& state) const
    {
      predicate_statet::const_iterator it=
	predicate_state.find(predicate);

      if (it==predicate_state.end()) {
	state=NOT_DEFINED;
	return false;
      }
      else {
	state=it->second; 
	return find(predicate, nr);
      }
    }



   
  // how many?
  unsigned size() const
   {
    return predicate_vector.size();
   }

  void get_pred_ids(std::pair<std::set<unsigned>, std::set<unsigned> > &pred_id_set_pair) const;
  
 protected:
  typedef std::map<predicatet, unsigned> predicate_mapt;
  typedef std::vector<predicate_mapt::iterator> predicate_vectort;
  

  predicate_mapt predicate_map;
  predicate_vectort predicate_vector;
  

  typedef std::map<predicatet, statet> predicate_statet;
  
  predicate_statet predicate_state;
  
  std::vector<bool> used_vector;
 };

std::ostream& operator<< (std::ostream& out,
                        const predicatest &predicates);

std::ostream& operator<< (std::ostream& out,
                          const std::set<predicatet> &ps);
#endif
