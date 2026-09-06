module main(input clk);
endmodule

module sub(input clk);
endmodule

bind main.no_such_instance sub s(.clk(clk));
