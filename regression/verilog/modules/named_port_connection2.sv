// The formal name in a named port connection is looked up in the
// port name space of the instantiated module, and hence may coincide
// with a typedef, interface, package or class name that happens to be
// visible at the point of instantiation.
module sub(
  input some_type,
  input some_if,
  input some_pkg,
  input some_class);

  initial assert (some_type && some_if && some_pkg && some_class);

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

  sub u(.some_type(1), .some_if(1), .some_pkg(1), .some_class(1));

endmodule
