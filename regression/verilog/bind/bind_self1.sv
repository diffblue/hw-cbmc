module main(input clk);
endmodule

// binding a module to itself would result in an unbounded recursion
bind main main m();
