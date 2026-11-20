// A hierarchical task call into a module instance.
module sub;
  logic [7:0] data;

  task t;
    begin
      data = 8'h12;
    end
  endtask
endmodule

module main;
  sub s();
  initial s.t();
  p1: assert property (s.data == 8'h12);
endmodule
