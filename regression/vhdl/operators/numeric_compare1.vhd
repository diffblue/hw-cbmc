-- IEEE 1076-2008 16.8.2: the relational operators of numeric_std
-- compare at full precision, including with an integer
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity numeric_compare1 is
  port(a : in unsigned(7 downto 0); b : in unsigned(3 downto 0); s : in signed(3 downto 0));
end;
architecture rtl of numeric_compare1 is
begin
  p1: assert not (a = 300);
  p2: assert a < 256;
  p3: assert (a = b) = (to_integer(a) = to_integer(b));
  p4: assert (s < 0) = (s(3) = '1');
  p5: assert (a + b) = (a + resize(b, 8));
  p6: assert s >= -8 and s <= 7;
end;
