module main;

  parameter int A [3] = '{ 10, 20, 30 };

  parameter Q = A[1];

  initial assert(Q == 20);

endmodule
