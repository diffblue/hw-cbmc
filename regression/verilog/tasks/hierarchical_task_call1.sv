// A hierarchical task call (1800-2017 13.3).
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
