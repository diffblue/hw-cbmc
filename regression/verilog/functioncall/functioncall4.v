module main;

  function vector_extract;
    input [63:0] vector;
    input integer index;
    vector_extract = vector[index];
  endfunction

  wire [63:0] some_value;
  wire return_value = vector_extract(some_value, 10);
  
  always assert p1: return_value == some_value[10];

endmodule
