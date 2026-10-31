module top;
  initial begin
    $fatal(1, "error: %d", 99);
  end
endmodule
