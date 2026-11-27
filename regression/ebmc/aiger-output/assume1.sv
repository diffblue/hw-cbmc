module main(input bit blocked);
  env: assume property (!blocked);
  safe: assert property (!blocked);
endmodule
