// IEEE 1800 2017 26.3 Referencing data in packages
// "The compilation of a package shall precede the compilation of
// scopes in which the package is imported."

// Hence, the below is an error

module top;
  int x = P::my_value;
endmodule

package P;
  parameter my_value = 123;
endpackage

