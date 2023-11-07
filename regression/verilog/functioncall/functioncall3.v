module main;

  function reduction_and;
  input [63:0] value;
  begin
    integer i;
    reduction_and = 1;
    for (i = 0; i < 64; i = i + 1)
      reduction_and = reduction_and & value[i];
    end
  endfunction // reduction_and

  wire [63:0] some_value;
  wire return_value = reduction_and(some_value);
  
  always assert p1: return_value == &some_value;

endmodule
