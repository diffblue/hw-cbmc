-- numeric_std: when the result of /, rem or mod with an integer operand
-- does not fit the vector, it is resized as by RESIZE, which for signed
-- keeps the sign bit and the low bits
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity signed_resize1 is
  port(y : out signed(3 downto 0));
end;
architecture rtl of signed_resize1 is
  constant a : signed(3 downto 0) := to_signed(-1, 4);
  constant one : signed(3 downto 0) := to_signed(1, 4);
  constant u : unsigned(3 downto 0) := to_unsigned(9, 4);
begin
  y <= a mod 12;
  p1: assert a mod 12 = 3;
  p2: assert 120 / one = 0;
  p3: assert 119 / one = 7;
  p4: assert (-120) / one = -8;
  -- IEEE 1076-2008 9.1: the sign operator binds weaker than /
  p5: assert -120 / one = 0;
  p6: assert a rem 12 = -1;
  p7: assert 300 / u = 1;
  p8: assert y = 3;
end;
