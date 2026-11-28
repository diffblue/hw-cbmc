-- the arithmetic operators of std_logic_unsigned on std_logic_vector
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
entity std_logic_unsigned1 is
  port(a : in std_logic_vector(3 downto 0));
end;
architecture rtl of std_logic_unsigned1 is
begin
  p1: assert a + 1 = a + "0001";
  p2: assert a < 16;
  p3: assert (a = 15) = (a = "1111");
end;
