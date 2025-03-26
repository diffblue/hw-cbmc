/******************************************************

Module: Some type synonyms and prototypes of functions
        operating on DNF/CNF formulas

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/

#pragma once

#include <deque>
#include <iosfwd>
#include <map>
#include <set>
#include <vector>

typedef std::vector<int> CUBE;
typedef std::vector<CUBE> DNF;
typedef std::vector<bool> bool_vector;
typedef std::vector<bool_vector> bool_matrix;
typedef std::vector <char> CCUBE;
typedef std::vector <CCUBE> CDNF;
typedef CUBE CLAUSE;
typedef std::set<int> SCUBE;
typedef DNF CNF;
typedef std::vector <float> FltCube;


#define BUF_SIZE 1000
#define MAX_NUM 20


/*========================

 C L A S S    comp_lits

=========================*/

class comp_lits {
public:
bool operator()(int x,int y)
  // compare absolute values of x and y
  {return abs(x) < abs(y);}
}; /* end of class comp_lits */

std::ostream &operator<<(std::ostream &os,CUBE const &v);
std::ostream &operator<<(std::ostream &os,CCUBE const &v);
std::ostream &operator<<(std::ostream &os,SCUBE &v);
std::ostream &operator<<(std::ostream &os,std::deque <int> const &v);
void print_dnf(DNF &D);
void print_dnf(DNF &D,int start,int finish);
void print_dnf1(DNF &D);
void print_dnf1(DNF &D,CCUBE &Active_cubes);
void print_dnf2(DNF &D,int start_num=0);
void print_dnf3(DNF &D,char *fname,int start_num=0);
void print_dnf(DNF &D,const char *fname);
// print DNF D in the dimacs format the number of variables is 
// computed by the value of the largest literal number
void print_dnf(DNF &D,char *fname); 
void print_dnf(DNF &D,FILE *fp); 
void print_dnf(DNF &D,int nvars,char *fname);// print DNF D in the dimacs format 
void print_dnf(DNF &D,CUBE &cube_nums);
void print_dnf(DNF &D,unsigned int threshold);
void print_dnf(DNF &D,char *fname,int start,int finish);
void print_dnf(DNF &D,char *fname,int num_vars);
void print_set(SCUBE &S);
int find_max_var(DNF &D);
void print_cube(CUBE &C);
void print_cube(FILE *fp,CCUBE &C);
void print_cube(FILE *fp,CUBE &C);
void print_cube(CCUBE &C);
void add_dnf(DNF &F1,DNF &F);
void fprint_cube(FILE *fp,CUBE &C);
void print_srt_cube(CUBE &C);
void fprint_srt_cube(FILE *fp,CUBE &C);
void print_srt_dnf(DNF &D);
void fprint_srt_dnf(DNF &D,char *fname);
void fprint_srt_dnf(DNF &D,const char *fname);


