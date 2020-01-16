/******************************************************

Module: Some type synonyms and prototypes of functions
        operating on DNF/CNF formulas

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
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
bool print_dnf(DNF &D,const char *fname);
// print DNF D in the dimacs format the number of variables is 
// computed by the value of the largest literal number
bool print_dnf(DNF &D,char *fname);
bool print_dnf(DNF &D,std::string &Name);
void print_dnf(DNF &D,std::ofstream &Out_str);
void print_dnf(DNF &D,CUBE &cube_nums);
void print_dnf(DNF &D,unsigned int threshold);
void print_set(SCUBE &S);
int find_max_var(DNF &D);
void print_cube(CUBE &C);
void print_cube(std::ofstream &Out_str,CCUBE &C);
void print_cube(std::ofstream &Out_str,CUBE &C);
void print_cube(CCUBE &C);
void add_dnf(DNF &F1,DNF &F);
void print_srt_cube(CUBE &C);
void print_srt_dnf(DNF &D);

//
//  
//
void fprint_cube(std::ofstream &Out_str,CUBE &C);

