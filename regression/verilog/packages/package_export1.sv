package inner;
  parameter int P = 1;
endpackage

package outer;
  import inner::P;
  export inner::P;
endpackage

module main;
endmodule
