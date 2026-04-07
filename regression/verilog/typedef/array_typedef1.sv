module main;

   typedef int some_array_type[3];
   some_array_type some_array;

   initial assert($size(some_array) == 3);

endmodule
