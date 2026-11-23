module sub #(parameter type data_t = int)(input data_t ingress, output data_t egress);

  assign egress = ingress;

endmodule

module main #(parameter type data_t = int)(input data_t ingress, output data_t egress);

  // The override value data_t refers to main's type parameter,
  // not to the parameter port of sub.
  sub #(.data_t(data_t)) dut(.ingress(ingress), .egress(egress));

  always_comb assert (egress == ingress);

endmodule
