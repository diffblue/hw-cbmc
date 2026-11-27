// The members of an interface port are elaboration-time constants for
// $bits: in a localparam, in the width of a declaration and of a port,
// and in the condition of a generate construct.
interface pif #(parameter W = 8);
  logic [W-1:0] a;
endinterface

module pu(pif s, input [$bits(s.a)-1:0] x);
  localparam N = $bits(s.a);
  logic [$bits(s.a)-1:0] copy;
  assign copy = s.a;

  if($bits(s.a) > 8) begin : wide
    p0: assert final (1);
  end
  else begin : narrow
    p0: assert final (0);
  end

  p1: assert final (N == 16);
  p2: assert final ($bits(copy) == 16);
  p3: assert final (copy == s.a);
  p4: assert final ($bits(x) == 16);
endmodule

module main;
  pif #(.W(16)) i();
  wire [15:0] w;
  pu u(.s(i), .x(w));
endmodule
