// Elements of an array of interface instances are bound to interface
// ports, also from within a generate loop.
interface pif #(parameter W = 8);
  logic [W-1:0] a;
endinterface

module pu #(parameter E = 0)(pif s);
  localparam N = $bits(s.a);
  p0: assert final (N == E);
endmodule

module main;
  pif #(.W(4)) arr[1:2]();
  pu #(4) u(.s(arr[2]));

  for(genvar i = 1; i <= 2; i++) begin : g
    // the instance precedes the interface it is bound to
    pu #(4 * i) u(.s(b));
    pif #(.W(4 * i)) b();
    pu #(4) v(.s(arr[i]));
  end
endmodule
