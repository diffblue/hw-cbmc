// A call of a function is an argument of another call of the same
// function. Evaluating the inner call assigns the function's parameters;
// this must not clobber the arguments of the outer call.
module main(input clk);

  function automatic [3:0] add(input [3:0] a, input [3:0] b);
    add = a + b;
  endfunction

  function automatic [3:0] sel(input [1:0] op, input [3:0] a, input [3:0] v);
    sel = (op == 2'd2) ? a + v : a;
  endfunction

  function automatic [3:0] ap(input bit v, input bit i, input [1:0] op,
                              input [3:0] vv, input bit x, input [3:0] a);
    ap = (v && i == x) ? sel(op, a, vv) : a;
  endfunction

  // the inner call is the second argument; unfixed, a takes the value
  // that the inner call assigns to it
  wire [3:0] r0 = add(4'd1, add(4'd5, 4'd4));         // 1 + 9 = 10
  wire [3:0] r1 = add(add(4'd1, 4'd2), add(4'd5, 4'd4)); // 3 + 9 = 12

  // the reported case: a nested call of a function that itself calls
  // another function
  wire [3:0] r2 = ap(1'b1, 1'b0, 2'd2, 4'd8, 1'b0,
                     ap(1'b0, 1'b0, 2'd0, 4'd0, 1'b0, 4'd0)); // 8

  // the same in an always block
  reg [3:0] q;
  always @(posedge clk)
    q <= add(4'd2, add(4'd5, 4'd4)); // 11

  // a recursive call, where a later actual reads a parameter of the
  // enclosing call: f(1, 2) = f(f(0, 1), 1) + 1 = f(1, 1) + 1 = 3
  function automatic [3:0] f(input [3:0] a, input [3:0] b);
    if(b == 0)
      f = a;
    else
      f = f(f(0, b - 1), a) + 1;
  endfunction

  wire [3:0] r3 = f(4'd1, 4'd2);

  // a task whose later input is a call of the function used in its body,
  // and a function called as a statement with a nested call of itself
  function automatic [3:0] inc(input [3:0] x);
    inc = x + 1;
  endfunction

  task t(input [3:0] a, input [3:0] b, output [3:0] y);
    y = inc(a) + b;
  endtask

  function automatic [3:0] add_out(input [3:0] a, input [3:0] b,
                                   output [3:0] o);
    o = a + b;
    add_out = o;
  endfunction

  reg [3:0] s1, s2, s3;
  always @(posedge clk) begin
    t(4'd1, inc(4'd5), s1);                  // inc(1) + 6 = 8
    add_out(4'd1, add_out(4'd2, 4'd3, s3), s2); // 1 + 5 = 6, s3 = 5
  end

  p0: assert property (@(posedge clk) r0 == 4'd10);
  p1: assert property (@(posedge clk) r1 == 4'd12);
  p2: assert property (@(posedge clk) r2 == 4'd8);
  p3: assert property (@(posedge clk) ##1 q == 4'd11);
  p4: assert property (@(posedge clk) r3 == 4'd3);
  p5: assert property (@(posedge clk) ##1 s1 == 4'd8);
  p6: assert property (@(posedge clk) ##1 s2 == 4'd6);
  p7: assert property (@(posedge clk) ##1 s3 == 4'd5);

endmodule
