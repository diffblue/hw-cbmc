// The parameter name in a named parameter assignment is looked up in the
// parameter name space of the instantiated module, and hence may coincide
// with a typedef, interface, package or class name that happens to be
// visible at the point of instantiation.
module sub #(
  parameter int some_type = 1,
  parameter int some_if = 2,
  parameter int some_pkg = 3,
  parameter int some_class = 4) ();

  initial assert (some_type == 10 && some_if == 20 &&
                  some_pkg == 30 && some_class == 40);

endmodule

typedef int some_type;

interface some_if;
  logic x;
endinterface

package some_pkg;
endpackage

class some_class;
endclass

module main;

  sub #(.some_type(10), .some_if(20), .some_pkg(30), .some_class(40)) u();

endmodule
