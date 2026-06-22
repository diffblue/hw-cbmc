module array_sorter(input clk, input [7:0] din, input load,
                   input [2:0] waddr,
                   output reg [7:0] min_val, output reg [7:0] max_val);

  reg [7:0] mem [0:7];
  reg [7:0] local_min, local_max;
  integer i;

  always @(posedge clk) begin
    if (load)
      mem[waddr] <= din;

    // Find min and max across the array
    local_min = mem[0];
    local_max = mem[0];
    for (i = 1; i < 8; i = i + 1) begin
      if (mem[i] < local_min)
        local_min = mem[i];
      if (mem[i] > local_max)
        local_max = mem[i];
    end

    min_val <= local_min;
    max_val <= local_max;
  end
endmodule
