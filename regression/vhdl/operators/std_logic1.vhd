-- The logical operators on std_logic, as concurrent assertions
-- over constant expressions.

library ieee;
use ieee.std_logic_1164.all;

entity std_logic1 is
end std_logic1;

architecture test of std_logic1 is
begin

  p1:  assert ('1' or   '0') = '1' report "1 or 0";
  p2:  assert ('0' or   '0') = '0' report "0 or 0";
  p3:  assert ('1' nor  '0') = '0' report "1 nor 0";
  p4:  assert ('0' nor  '0') = '1' report "0 nor 0";
  p5:  assert ('1' and  '0') = '0' report "1 and 0";
  p6:  assert ('1' and  '1') = '1' report "1 and 1";
  p7:  assert ('1' nand '0') = '1' report "1 nand 0";
  p8:  assert ('1' nand '1') = '0' report "1 nand 1";
  p9:  assert ('1' xor  '0') = '1' report "1 xor 0";
  p10: assert ('1' xnor '0') = '0' report "1 xnor 0";
  p11: assert (not '0')      = '1' report "not 0";

end test;
