-- numeric_std 16.8.4 and std_logic_unsigned define the arithmetic
-- operators on vectors of different lengths, so a literal operand
-- keeps its own length; the result has the longer length
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;
entity numeric_literal_arith1 is
  port(y : out unsigned(3 downto 0));
end;
architecture rtl of numeric_literal_arith1 is
  signal cnt : std_logic_vector(3 downto 0) := "0010";
  signal u : unsigned(3 downto 0) := "0010";
  signal s : signed(3 downto 0) := "1110";
  constant u3 : unsigned := u * "11";
begin
  y <= u + "1";
  p1: assert cnt + "1" = "0011";
  p2: assert u + "1" = "0011";
  p3: assert "1" + u = 3;
  p4: assert u - "11" = 15;
  p5: assert u * "11" = 6;
  p6: assert u3'length = 6;
  -- a one-element signed literal is -1, and is sign extended
  p7: assert s + "01" = -1;
  p8: assert s + "1" = -3;
  p9: assert y = 3;
end;
