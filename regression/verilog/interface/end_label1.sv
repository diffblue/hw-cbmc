// End label after endinterface, IEEE 1800-2017 A.1.3.
interface ifc;
  parameter int W = 8;
  logic [W-1:0] data;
endinterface : ifc

module main;

  ifc i();

  initial p0: assert (i.W == 8);

endmodule
