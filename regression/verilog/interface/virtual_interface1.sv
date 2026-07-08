// Virtual interface (IEEE 1800-2017 25.9)
interface simple_if;
  logic data;
endinterface

module main;
  simple_if sif();
  virtual simple_if vif;
  initial begin
    vif = sif;
  end
endmodule
