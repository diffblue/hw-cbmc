-- IEEE 1076-2008 9.3.5: a qualified expression of an unconstrained
-- array type takes its length from the literal
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity qualified_unsigned1 is
  port(y : out unsigned(3 downto 0));
end;
architecture rtl of qualified_unsigned1 is
begin
  y <= unsigned'("0011");
  p1: assert y = 3;
  p2: assert unsigned'("0011")'length = 4;
end;
