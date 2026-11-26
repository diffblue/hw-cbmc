-- numeric_std multiplication yields the sum of the operand lengths
-- (IEEE 1076-2008 16.8.2); arrays of different lengths are never equal (9.2.3).
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity numeric_std2 is
  port(a, b : in unsigned(3 downto 0); x : in std_logic_vector(0 downto 0); y : in std_logic_vector(1 downto 0));
end;
architecture rtl of numeric_std2 is
  signal p : unsigned(7 downto 0);
  signal q : unsigned(7 downto 0);
begin
  p <= a * b;
  q <= a * 3;
  p0: assert p = a * b;
  p1: assert not (x = y);       -- different lengths: never equal
  p2: assert to_integer(p) = to_integer(a) * to_integer(b);
end;
