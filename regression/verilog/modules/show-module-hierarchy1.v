module leaf1;
endmodule

module leaf2;
endmodule

module inner;
  leaf1 leaf1_instance();
  leaf2 leaf2_instance();
endmodule

module main;
  inner inner_instance1();
  inner inner_instance2();
endmodule
