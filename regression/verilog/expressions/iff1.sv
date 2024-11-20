module main;

  // logical equivalence
  // 1800-2017 11.4.7
  property1: assert final ((1<->1)===1);
  property2: assert final ((1<->2)===1);
  property3: assert final ((1<->0)===0);
  property4: assert final ((0<->0)===1);
  property5: assert final ((3.145<->1)===1); // works on real
  property6: assert final ((1'b1<->1'bx)===1'bx);
  property7: assert final ((2'bxx<->2'bxx)===1'bx);

endmodule
