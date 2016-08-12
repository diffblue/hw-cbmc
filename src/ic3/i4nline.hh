/******************************************************

Module: Inline functions

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
/*====================================

  C O N V _ T O _ M L I T 

  ==================================*/
inline Mlit conv_to_mlit(int lit)
{

  if (lit < 0) return(Minisat::mkLit(-lit-1,true));
  return(Minisat::mkLit(lit-1,false));

} /* end of function conv_to_mlit */

/*================================

  M L I T _T O _ L I T

  ===============================*/
inline int mlit_to_lit(Minisat::Solver *Slvr,Mlit L)
{
  assert(var(L) < Slvr->nVars());
  int lit = var(L)+1;
  if (sign(L)) lit = -lit;
  return(lit);
} /* end of function mlit_to_lit */
