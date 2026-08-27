typedef struct {
  logic field1;
  logic field2;
} structure_t;

module main(input wire clk);

  structure_t s;

  // The fields of a struct may be assigned in different
  // always constructs.
  always @(posedge clk) begin
    s.field1 <= 0;
  end

  always @(posedge clk) begin
    s.field2 <= 1;
  end

  p1: assert property (@(posedge clk) ##1 s.field1 == 0);
  p2: assert property (@(posedge clk) ##1 s.field2 == 1);

endmodule
