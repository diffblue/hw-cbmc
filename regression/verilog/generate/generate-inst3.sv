module submodule(dout, din);

  parameter DATA_WIDTH = 1;

  input [DATA_WIDTH-1:0] din;
  output [DATA_WIDTH-1:0] dout;

  assign dout = din;

endmodule

module main(input [7:0] in);

  parameter WIDTH = 4;

  wire [2*WIDTH-1:0] out;

  // The genvar is used in the part select of the port connections.
  // It must be evaluated per iteration, and not with the value the
  // genvar has once the loop has terminated.
  generate
    genvar i;

    for(i = 0; i < 2; i = i + 1) begin : my_block
      submodule #(.DATA_WIDTH(WIDTH)) my_instance(
        .dout(out[i*WIDTH +: WIDTH]),
        .din(in[i*WIDTH +: WIDTH]));
    end
  endgenerate

  // should pass
  property1: assert final (out == in);

endmodule
