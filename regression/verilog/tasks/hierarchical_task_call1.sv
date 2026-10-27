// A hierarchical task call, which is not supported.
module sub;
  task t;
    begin
    end
  endtask
endmodule

module main;
  sub s();
  initial s.t();
endmodule
