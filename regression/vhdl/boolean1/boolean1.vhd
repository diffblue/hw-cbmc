-- The logical operators on boolean, as concurrent assertions
-- over constant expressions.

entity boolean1 is
end boolean1;

architecture test of boolean1 is
begin

  p1:  assert (true  or   false) = true  report "true or false";
  p2:  assert (false or   false) = false report "false or false";
  p3:  assert (true  nor  false) = false report "true nor false";
  p4:  assert (false nor  false) = true  report "false nor false";
  p5:  assert (true  and  false) = false report "true and false";
  p6:  assert (true  and  true)  = true  report "true and true";
  p7:  assert (true  nand false) = true  report "true nand false";
  p8:  assert (true  nand true)  = false report "true nand true";
  p9:  assert (true  xor  false) = true  report "true xor false";
  p10: assert (true  xnor false) = false report "true xnor false";
  p11: assert (not false)        = true  report "not false";

end test;
