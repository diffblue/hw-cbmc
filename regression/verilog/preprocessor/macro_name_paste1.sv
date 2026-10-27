// The name of a macro that is called is built with `` (IEEE 1800-2017
// 22.5.1). Reduced from the UVM library (uvm_object_defines.svh):
// `m_uvm_``TYPE``_resize(ARG, local_size__)
`define m_x_resize(A) A + 1
`define call(TYPE, A) `m_``TYPE``_resize(A)

module main;
  p0: assert final (`call(x, 1) == 2);
endmodule
