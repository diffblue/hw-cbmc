-- IEEE 1076-2008 9.2.7: the result of mod has the sign of the right
-- operand; numeric_std "mod" on signed has the length of the right
-- operand
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity signed_mod1 is
  port(y : out signed(3 downto 0));
end;
architecture rtl of signed_mod1 is
  constant a : signed(3 downto 0) := to_signed(3, 4);
  constant b : signed(3 downto 0) := to_signed(5, 4);
  constant na : signed(3 downto 0) := to_signed(-3, 4);
  constant nb : signed(3 downto 0) := to_signed(-5, 4);
begin
  y <= a mod b;
  p1: assert a mod b = 3;
  p2: assert na mod b = 2;
  p3: assert a mod nb = -2;
  p4: assert na mod nb = -3;
  p5: assert a rem b = 3;
  p6: assert na rem b = -3;
  p7: assert a rem nb = 3;
  p8: assert na rem nb = -3;
  p9: assert y = 3;
  p10: assert a mod 20 = 3;
  p11: assert na rem 20 = -3;
end;
