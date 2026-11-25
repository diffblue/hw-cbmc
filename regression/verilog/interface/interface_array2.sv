// The index of an element of an array of interface instances is an
// elaboration-time constant, which may be an expression over a genvar.
interface pif;
  logic [7:0] a;
endinterface

module main;
  pif arr[0:1]();
  assign arr[0].a = 8'd10;
  assign arr[1].a = 8'd11;

  for(genvar i = 1; i <= 2; i++) begin : g
    p0: assert final (arr[i - 1].a == 8'd9 + i);
  end
endmodule
