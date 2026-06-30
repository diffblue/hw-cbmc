module top;
  integer x;
  initial begin
    x = 42;
    $display("x = %d", x);
    $finish;
  end
endmodule
