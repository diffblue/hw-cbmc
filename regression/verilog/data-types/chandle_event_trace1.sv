// A counterexample trace of a design with chandle and event variables.
module main(input x);
  chandle c;
  event e;
  p0: assert final (x);   // fails
endmodule
