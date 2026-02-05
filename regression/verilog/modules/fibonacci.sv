// this uses a recursive module to get the Fibonacci sequence

module fibonacci #(parameter integer N = 0);

  wire integer value;
  
  generate
    if(N <= 0)
      assign value = 0;
    else if(N == 1)
      assign value = 1;
    else begin : rec
      fibonacci #(N-1) F1();
      fibonacci #(N-2) F2();
      assign value = F1.value + F2.value;
    end
  endgenerate

endmodule

module fibonacci_tb;

  fibonacci #(0) f0();
  fibonacci #(1) f1();
  fibonacci #(2) f2();
  fibonacci #(3) f3();
  fibonacci #(4) f4();
  fibonacci #(5) f5();
  fibonacci #(6) f6();
  fibonacci #(7) f7();
  fibonacci #(8) f8();
  fibonacci #(9) f9();
  fibonacci #(10) f10();

  initial begin
    #1;
    $display("F(0)  = %0d", f0.value);
    $display("F(1)  = %0d", f1.value);
    $display("F(2)  = %0d", f2.value);
    $display("F(3)  = %0d", f3.value);
    $display("F(4)  = %0d", f4.value);
    $display("F(5)  = %0d", f5.value);
    $display("F(6)  = %0d", f6.value);
    $display("F(7)  = %0d", f7.value);
    $display("F(8)  = %0d", f8.value);
    $display("F(9)  = %0d", f9.value);
    $display("F(10) = %0d", f10.value);
  end

  initial begin
    #1;
    assert(f0.value == 0);
    assert(f1.value == 1);
    assert(f2.value == 1);
    assert(f3.value == 2);
    assert(f4.value == 3);
    assert(f5.value == 5);
    assert(f6.value == 8);
    assert(f7.value == 13);
    assert(f8.value == 21);
    assert(f9.value == 34);
    assert(f10.value == 55);
  end

endmodule
