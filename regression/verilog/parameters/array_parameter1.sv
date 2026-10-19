module main;

  typedef int int_array [3];
  parameter int_array A = '{ 10, 20, 30 };

  parameter Q = A[1];

  initial assert(Q == 20);

endmodule
