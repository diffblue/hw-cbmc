// An interface port connected to an interface instance inside a named
// generate block, referenced hierarchically (1800-2017 27.6).
interface A #(parameter W = 1);
  logic [W-1:0] d;
endinterface

module leaf(A p, output [7:0] y);
  assign y = p.d;
endmodule

module main(input [7:0] x);
  wire [7:0] y;

  for(genvar g = 0; g < 1; g++) begin : G
    A #(.W(8)) a();
    assign a.d = x;
  end

  leaf l(.p(G[0].a), .y(y));

  p0: assert final (y == x);
endmodule
