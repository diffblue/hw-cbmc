/*******************************************************************\

Module: Diameter Test

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <iostream>

#include "diameter.h"

/*******************************************************************\

Function: comparator

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt comparator(propt &solver, const bvt &a, const bvt &b)
{
  assert(a.size()==b.size());
  assert(a.size()>0);

  bvt xors;
  xors.resize(a.size());

  for(unsigned i=0; i<a.size(); i++)
    xors[i]=solver.lxor(a[i], b[i]);

  literalt literal=solver.lor(xors);

  return neg(literal);
}

/*******************************************************************\

Function: simple_diameter

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt simple_diameter(propt &solver, const std::vector<bvt> &states)
{
  bvt comparators;

  assert(states.size()>1);

  comparators.reserve(states.size()*states.size());

  for(unsigned i=0; i<states.size(); i++)
    for(unsigned j=i+1; j<states.size(); j++)
      comparators.push_back(comparator(solver, states[i], states[j]));

  return solver.lnot(solver.lor(comparators));
}

/*******************************************************************\

Function: gen_carry

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt gen_carry(propt &solver, literalt a, literalt b, literalt c)
{
  bvt clause;

  literalt x=solver.new_variable();

  /*
  carry_correct: LEMMA
    (    a OR     b OR          NOT x) AND
    (    a OR NOT b OR     c OR NOT x) AND
    (    a OR NOT b OR NOT c OR     x) AND
    (NOT a OR     b OR     c OR NOT x) AND
    (NOT a OR     b OR NOT c OR     x) AND
    (NOT a OR NOT b OR              x)
    IFF
    (x=((a AND b) OR (a AND c) OR (b AND c)));
  */

  clause.resize(3);
  clause[0]=a;
  clause[1]=b;
  clause[2]=neg(x);
  solver.lcnf(clause);

  clause.resize(4);
  clause[0]=a;
  clause[1]=neg(b);
  clause[2]=c;
  clause[3]=neg(x);
  solver.lcnf(clause);

  clause.resize(4);
  clause[0]=a;
  clause[1]=neg(b);
  clause[2]=neg(c);
  clause[3]=x;
  solver.lcnf(clause);

  clause.resize(4);
  clause[0]=neg(a);
  clause[1]=b;
  clause[2]=c;
  clause[3]=neg(x);
  solver.lcnf(clause);

  clause.resize(4);
  clause[0]=neg(a);
  clause[1]=b;
  clause[2]=neg(c);
  clause[3]=x;
  solver.lcnf(clause);

  clause.resize(3);
  clause[0]=neg(a);
  clause[1]=neg(b);
  clause[2]=x;
  solver.lcnf(clause);

  return x;
}

/*******************************************************************\

Function: ordering

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt ordering(propt &solver, const bvt &a, const bvt &b)
{
  assert(a.size()==b.size());
  assert(a.size()>0);

  literalt carry=solver.lor(a[0], neg(b[0]));

  for(unsigned i=1; i<a.size(); i++)
    carry=gen_carry(solver, a[i], neg(b[i]), carry);

  return carry;
}

/*******************************************************************\

Function: swap

  Inputs:

 Outputs:

 Purpose: x=c?a:b

\*******************************************************************/

literalt select(propt &solver, literalt a, literalt b, literalt c)
{
  /*
  swap_correct: LEMMA
    (NOT x OR     c OR b) AND 
    (NOT x OR NOT c OR a) AND
    (NOT a OR NOT c OR x) AND
    (NOT b OR     c OR x)
    IFF
    x=((a AND c) OR (b AND NOT c));
  */

  bvt clause;
  clause.resize(3);

  literalt x=solver.new_variable();

  clause[0]=neg(x);
  clause[1]=c;
  clause[2]=b;
  solver.lcnf(clause);

  clause[0]=neg(x);
  clause[1]=neg(c);
  clause[2]=a;
  solver.lcnf(clause);

  clause[0]=neg(a);
  clause[1]=neg(c);
  clause[2]=x;
  solver.lcnf(clause);

  clause[0]=neg(b);
  clause[1]=c;
  clause[2]=x;
  solver.lcnf(clause);

  return x;
}

/*******************************************************************\

Function: swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt swap(propt &solver, const bvt &a, const bvt &b, literalt c)
{
  assert(a.size()==b.size());
  assert(a.size()>0);

  bvt result;
  result.resize(a.size());

  for(unsigned i=0; i<a.size(); i++)
    result[i]=select(solver, a[i], b[i], c);

  return result;
}

/*******************************************************************\

Function: compare

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define bool unsigned
#define ASCENDING 1   // sorting direction
#define DESCENDING 0

// Ein Vergleicher wird durch die Prozedur compare modelliert. Der Parameter
// dir gibt die Sortierrichtung an. Die Elemente a[i] und a[j] werden
// vertauscht, wenn dir = ASCENDING und (a[i] > a[j]) = true oder wenn dir =
// DESCENDING und (a[i] > a[j]) = false gilt.

unsigned compare_counter;

void compare(propt &solver, std::vector<bvt> &v, int i, int j, bool dir)
{
  // if (dir==(a[i]>a[j]))
  // {
  //     int h=a[i];
  //     a[i]=a[j];
  //     a[j]=h;
  // }

  compare_counter++;

  #if 0
  literalt ordering_lit=ordering(solver, v[i], v[j]);
  
  if(!dir)
    ordering_lit=neg(ordering_lit);
  
  bvt tmpj=swap(solver, v[i], v[j], ordering_lit);
  bvt tmpi=swap(solver, v[j], v[i], ordering_lit);

  v[i]=tmpi;
  v[j]=tmpj;

  #else
  // on-line version

  bvt &a=v[i];
  bvt &b=v[j];

  assert(a.size()==b.size());

  literalt s=const_literal(false), // true: sorting direction fixed
           t=const_literal(false); // true: sorting direction is *b*

  for(unsigned i=0; i<a.size(); i++)
  {
    literalt _a=a[i], _b=b[i];

    t=select(solver, t, _b, s);
    s=solver.lor(solver.lxor(_a, _b), s);

    literalt ordering_lit(t);
    if(!dir) ordering_lit=neg(ordering_lit);

    literalt oa=select(solver, _a, _b, ordering_lit);
    literalt ob=select(solver, _b, _a, ordering_lit);
    a[i]=oa;
    b[i]=ob;
  }

  #endif  
}

/*******************************************************************\

Function: bitonicMerge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// Die Prozedur bitonicMerge sortiert rekursiv eine bitonische Folge a. Die zu
// sortierende Folge beginnt am Index lo, die Anzahl der Elemente ist cnt, die
// Sortierrichtung ist aufsteigend, wenn dir = ASCENDING, sonst absteigend.  
 
void bitonicMerge(propt &solver, std::vector<bvt> &v, int lo, int cnt, bool dir, int high)
{
    if (cnt>1)
    {
        int k=cnt/2, i;
        
        assert(k+k==cnt); // must be power of two
        
        for (i=lo; i<lo+k; i++)
          if(i+k<=high)
            compare(solver, v, i, i+k, dir);
            
        bitonicMerge(solver, v, lo, k, dir, high);
        bitonicMerge(solver, v, lo+k, k, dir, high);
    }
}

/*******************************************************************\

Function: power2

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static unsigned power2(unsigned i)
{
  unsigned result;
   
  for(result=1; result<i; result*=2);
     
  return result;
}

/*******************************************************************\

Function: bitonicSort

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// Die Prozedur bitonicSort erzeugt zunaechst eine bitonische Folge, indem sie
// die beiden Haelften der Folge gegenlaeufig sortiert (durch zwei rekursive
// Aufrufe von bitonicSort). Danach sortiert sie die bitonische Folge durch
// Aufruf von bitonicMerge.  
 
void bitonicSort(propt &solver, std::vector<bvt> &v, int lo, int cnt, bool dir)
{
    if (cnt>1)
    {
        if(cnt==4)
        {
          // five comparators is the optimal size for 4 inputs
          compare(solver, v, lo+0, lo+1, dir);
          compare(solver, v, lo+2, lo+3, dir);
          compare(solver, v, lo+1, lo+3, dir);
          compare(solver, v, lo+0, lo+2, dir);
          compare(solver, v, lo+1, lo+2, dir);
          return;
        }

        int pow=power2(cnt);
        int k=pow/2;
        bitonicSort(solver, v, lo, k, !dir);
        bitonicSort(solver, v, lo+k, cnt-k, dir);
        bitonicMerge(solver, v, lo, pow, dir, lo+cnt-1);
    }
}

/*******************************************************************\

Function: sort_states

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void sort_states(propt &solver, const std::vector<bvt> &states, std::vector<bvt> &sorted_states)
{
  sorted_states=states;

  compare_counter=0;
  bitonicSort(solver, sorted_states, 0, sorted_states.size(), ASCENDING);
  std::cout << "compare_counter: " << compare_counter << '\n';
}

/*******************************************************************\

Function: efficient_diameter

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt efficient_diameter(propt &solver, const std::vector<bvt> &states)
{
  bvt comparators;
  std::vector<bvt> sorted_states;

  assert(states.size()>1);

  sort_states(solver, states, sorted_states);

  comparators.resize(sorted_states.size()-1);

  for(unsigned i=0; i<sorted_states.size()-1; i++)
    comparators[i]=
    comparator(solver, sorted_states[i], sorted_states[i+1]);

  return solver.lnot(solver.lor(comparators));
}
