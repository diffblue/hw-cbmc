// Port expressions. The type of the port is derived
// from the type of the expression.
// Not supported by Icarus 12, VCS 2023.03, Xcelium 23.09.
// Works with Questa 2024.3, Riviera Pro 2023.04.
module M(.some_input(data[7:0]));

  reg [31:0] data;

  initial #1 assert (data[7:0] == 123);

endmodule

module main;

  M my_instance(.some_input(123));

endmodule
