// Two interface instances bound to each other's interface ports.
interface B(B other);
endinterface

module main;
  B b1(.other(b2));
  B b2(.other(b1));
endmodule
