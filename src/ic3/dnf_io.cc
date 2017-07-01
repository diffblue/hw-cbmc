/******************************************************

Module: Functions dealing with
        DNF/CNF formulas

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <assert.h>
#include <iostream>
#include <set>
#include <queue>
#include <algorithm>
#include <map>
#include <stdio.h>
#include "dnf_io.hh"
#include "s0hared_consts.hh"

/*========================================


  F I N D _ M A X _ V A R

  returns the maximal (order) number
  of a variable occuring in cubes  of D
  incremented by 1

  =========================================*/
int find_max_var(DNF &D)

{int max=0;
  unsigned int i,j;
  CUBE cube;

  for (i = 0; i < D.size();i++)
    {cube = D[i];
      for (j = 0; j < cube.size();j++)
	if (abs(cube[j]) >  max)
	  max = abs(cube[j]);
    }
  return(max);

} /* end of function find_max_var */

/*========================================


  F I N D _ M A X _ V A R

  returns the maximal (order) number
  of a variable occuring in cubes  of D
  that ARE NOT marked in marked_sat
  =========================================*/
int find_max_var(DNF &D,bool_vector &marked_sat)

{int max=0;
  unsigned int i,j;
  CUBE cube;

  for (i = 0; i < D.size();i++)
    {if (marked_sat[i])
	continue;
      cube = D[i];
      for (j = 0; j < cube.size();j++)
	if (abs(cube[j]) >  max)
	  max = abs(cube[j]);
    }
  return(max);

} /* end of function find_max_var */



/*============================================


  P R I N T _ S E T 

  =============================================*/
void print_set(SCUBE &s)

{SCUBE::iterator i;

  for (i=s.begin();i != s.end();i++)
    std::cout << *i << " ";

  std::cout << std::endl;
} /* end of function print_set */

/*===========================

  P R I N T _ C U B E

  ==========================*/
void print_cube(CUBE &C) {
  for (size_t i=0; i < C.size(); i++) {
    if (i > 0) printf(" ");
    printf("%d",C[i]);
  }
  printf(" 0\n");
} /* end of function print_cube */


/*==============================

  P R I N T _ C U B E 

  ================================*/
void print_cube(CCUBE &C)
{
  for (size_t i=0; i < C.size(); i++)
    printf("%d ",C[i]);

  printf("\n");
}/* end of function print_cube */

/*===========================

  P R I N T _ C U B E 

  ===========================*/
void print_cube(FILE *fp,CCUBE &C)
{
  for (size_t i=0; i < C.size(); i++)
    fprintf(fp,"%d ",C[i]);

  fprintf(fp,"\n");
}/* end of function print_cube */

/*===========================

  P R I N T _ C U B E 

  ===========================*/
void print_cube(FILE *fp,CUBE &C)
{
  for (size_t i=0; i < C.size(); i++)
    fprintf(fp,"%d ",C[i]);

}/* end of function print_cube */






 
/*==========================================

  O P E R A T O R < <

  for type SCUBE

  ===========================================*/

std::ostream &operator<<(std::ostream &os,SCUBE &v)
{SCUBE::iterator i;
  for (i=v.begin();i!= v.end();i++)
    std::cout << *i << " ";
  std::cout << std::endl;
  return(os);
}

/*==============================

  O P E R A T O R < <

  for type vector<int>
 
  ==========================*/

std::ostream &operator<<(std::ostream &os,CUBE const &v)
{CUBE:: const_iterator i;
  for (i=v.begin();i!= v.end();i++)
    if (i == v.begin()) std::cout << *i;
    else std::cout << " " << *i;
  return(os);
}

/*========================

  O P E R A T O R < <

  for type vector<char>

  ========================*/
std::ostream &operator<<(std::ostream &os,CCUBE const &v)
{CCUBE:: const_iterator i;
  for (i=v.begin();i!= v.end();i++)
    if (i == v.begin()) printf("%d",*i);
    else printf("%d",*i);
  return(os);
}




/*=============================

  P R I N T _ D N F

  Prints the cubes that whose
  numbers are in cube_nums

  ===========================*/
void print_dnf(DNF &D,CUBE &Cube_nums)

{
  printf("p cnf %d %d\n",find_max_var(D),(int) Cube_nums.size());
  for (size_t i = 0; i < Cube_nums.size();i++)
    print_cube(D[Cube_nums[i]]);
} /* end of function print_dnf */



/*==============================


  P R I N T _ D N F 1

  Prints the cubes that ARE
  MARKED in active_cubes
  ==============================*/
void print_dnf1(DNF &D,CCUBE &Active_cubes)
{

  for (size_t i = 0; i < D.size();i++)
    if (Active_cubes[i]) print_cube(D[i]);
    
} /* end of function print_dnf1 */

/*==============================

  P R I N T _ D N F

  prints D   to the file "fname" 
  in the dimacs format
   
  ===============================*/
void print_dnf(DNF &D,FILE *fp)
{
  fprintf(fp,"p cnf %d %d\n",find_max_var(D),(int) D.size());
  for (size_t i = 0; i < D.size();i++)
    fprint_cube(fp,D[i]);
 
} /* end of function print_dnf */


/*=================================

  P R I N T _ D N F

  prints D   to the file "fname" 
  in the dimacs format
   
  ==================================*/
void print_dnf(DNF &D,char *fname)
{ FILE *fp;

  fp = fopen(fname,"w");
  if (fp == NULL) {
    std::cout << "cannot open file " << fname << std::endl;
    throw(ERROR2);}
     
   
  print_dnf(D,fp);  
  fclose(fp);

} /* end of function print_dnf */

/*=======================
   
  P R I N T _ D N F

  ======================*/

void print_dnf(DNF &D,const char *fname)
{
  print_dnf(D,(char *) fname);
} /* end of function print_dnf */

/*=================================

  P R I N T _ D N F

  prints D   to the file "fname" 
  in the dimacs format
   
  ==================================*/
void print_dnf(DNF &D,int nvars,char *fname)

{ 
  FILE *fp;

  fp = fopen(fname,"w");
  if (fp == NULL) 
    {std::cout << "cannot open file " << fname << std::endl;
      throw(ERROR2);
    }
   
  fprintf(fp,"p cnf %d %d\n",nvars,(int) D.size());
  for (size_t i = 0; i < D.size();i++)
    fprint_cube(fp,D[i]);
  fclose(fp);
} /* end of function print_dnf */

/*=================================

  P R I N T _ D N F

  Print DNF in the DIMACS format to 
  the standard output

  ==================================*/
void print_dnf(DNF &D) {

  printf("p cnf %d %d\n",find_max_var(D),(int) D.size());
  for (size_t i = 0; i < D.size();i++)
    print_cube(D[i]);
} /* end of function print_dnf */

/*=====================================================

  P R I N T _ D N F

  Print a subset of cubes of D  in the DIMACS format to 
  the standard output. This subset consists of cubes
  whose numbers are greater or equal   than start and 
  smaller than finish
  ======================================================*/
void print_dnf(DNF &D,int start,int finish) {

  // note that in the line below we compute find_max_var for
  //   the whole DNF formula
  printf("p cnf %d %d\n",find_max_var(D),finish-start); 
  for (int i = start; i < finish;i++)
    print_cube(D[i]);
} /* end of function print_dnf */

/*=================================

  P R I N T _ D N F

  Prints the cubes whose length is 
  not greater than threshold.
  ==================================*/
void print_dnf(DNF &D,unsigned int threshold)
{
  printf("p cnf %d %d\n",find_max_var(D),(int) D.size());
  for (size_t i = 0; i < D.size();i++)
    if (D[i].size() <= threshold)
      print_cube(D[i]);

} /* end of function print_dnf */

   
/*=================================

  P R I N T _ D N F 1

  In contrast to print_dnf 
  prints cubes in the reverse order
  ==================================*/
void print_dnf1(DNF &D) {
  size_t D_size=D.size();
  for (size_t i = 0; i < D_size; i++)
    print_cube(D[D_size-i-1]);
} /* end of function print_dnf1 */

/*=============================

  P R I N T _ D N F 2

  Prints numbers of cubes

  ===============================*/
void print_dnf2(DNF &D,int start_num)

{
  printf("p cnf %d %d\n",find_max_var(D),(int) D.size());
  for (size_t i = 0; i < D.size();i++) {
    std::cout << start_num+i << "/ ";
    print_cube(D[i]);
  }
} /* end of function print_dnf2 */

/*============================

  P R I N T _ D N F 3

  Prints numbers of cubes

  ==========================*/
void print_dnf3(DNF &D,char *fname,int start_num)

{CUBE cube;

  FILE *fp = fopen(fname,"w");
  assert(fp != NULL);

  fprintf(fp,"p cnf %d %d\n",find_max_var(D),(int) D.size());
  for (size_t i = 0; i < D.size();i++)   {
    fprintf(fp,"%zu/ ", start_num+i);
    fprint_cube(fp,D[i]);
  }
  fclose(fp);
} /* end of function print_dnf3 */



/*===========================

  F P R I N T _ C U B E

  ==========================*/
void fprint_cube(FILE *fp,CUBE &C) {
  for (size_t i=0; i < C.size(); i++) {
    if (i > 0) fprintf(fp," ");
    fprintf(fp,"%d",C[i]);
  }
  fprintf(fp," 0\n");
} /* end of function fprint_cube */


/*=====================

  A D D _ D N F

  add DNF F to F1
  =====================*/
void add_dnf(DNF &F1,DNF &F)
{
  for (size_t i = 0; i < F.size();i++)
    F1.push_back(F[i]);
} /* end of function add_dnf */

/*=========================================================

  P R I N T _ D N F

  Print a subset of cubes of D  in the DIMACS format to 
  the standard output. This subset consists of cubes
  whose numbers are greater or equal   than start and 
  smaller than finish
  ======================================================*/
void print_dnf(DNF &D,char *fname,int start,int finish)
{
  
  FILE *fp;

  fp = fopen(fname,"w");
  if (fp == NULL) {
    printf("cannot open file %s\n",fname);
    throw(ERROR2);}
     
  // note that in the line below we compute find_max_var for
  //   the whole DNF formula
  fprintf(fp,"p cnf %d %d\n",find_max_var(D),finish-start); 

  for (int i = start; i < finish;i++)
    fprint_cube(fp,D[i]);
   
} /* end of function print_dnf */

/*========================

  O P E R A T O R < <

  for type deque<int>
 
  ======================*/
std::ostream &operator<<(std::ostream &os,std::deque <int> const &v)
{std::deque <int>:: const_iterator i;
  for (i=v.begin();i!= v.end();i++)
    std::cout << *i << " ";  
  return(os);
}

/*=================================

  P R I N T _ D N F

  prints D   to the file "fname" 
  in the dimacs format
   
  ==================================*/
void print_dnf(DNF &D,char *fname,int num_vars)

{ FILE *fp;

  fp = fopen(fname,"w");
  if (fp == NULL) {
    std::cout << "cannot open file " << fname << std::endl;
    throw(ERROR2);
  }
   
  fprintf(fp,"p cnf %d %d\n",num_vars,(int) D.size());
  for (size_t i = 0; i < D.size();i++)
    fprint_cube(fp,D[i]);

  fclose(fp);
} /* end of function print_dnf */


/*================================

  P R I N T _ S R T _ C U B E

  =================================*/
void print_srt_cube(CUBE &C) {

  CUBE A = C;
  sort(A.begin(),A.end());
  print_cube(A);

} /* end of function print_srt_cube */

/*================================

  F P R I N T _ S R T _ C U B E

  =================================*/
void fprint_srt_cube(FILE *fp,CUBE &C) {

  CUBE A = C;
  sort(A.begin(),A.end());
  fprint_cube(fp,A);

} /* end of function fprint_srt_cube */

/*================================

  P R I N T _ S R T _ D N F

  =================================*/
void print_srt_dnf(DNF &D) {


  printf("p cnf %d %d\n",find_max_var(D),(int) D.size());
  for (size_t i=0; i < D.size(); i++)
    print_srt_cube(D[i]);

} /* end of function print_srt_dnf */

/*================================

  F P R I N T _ S R T _ D N F

  =================================*/
void fprint_srt_dnf(DNF &D,char *fname) {

  FILE *fp = fopen(fname,"w");
  if (fp == NULL) {
    printf("failed to open file %s\n",fname);
    throw(ERROR2);
  }

  fprintf(fp,"p cnf %d %d\n",find_max_var(D),(int) D.size());
  for (size_t i=0; i < D.size(); i++)
    fprint_srt_cube(fp,D[i]);

  fclose(fp);
} /* end of function fprint_srt_dnf */


/*================================

  F P R I N T _ S R T _ D N F

  =================================*/
void fprint_srt_dnf(DNF &D,const char *fname) {

  fprint_srt_dnf(D,(char *) fname);

} /* end of function fprint_srt_dnf */
