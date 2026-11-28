library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity cmp_int is
  port (clk : in std_logic; n : in integer);
end entity;

architecture rtl of cmp_int is
  signal u : unsigned(7 downto 0) := x"00";
  constant big : integer := 256;
begin
  -- numeric_std: u < 256 is always TRUE for an 8-bit u; expected PROVED
  p0: assert u < big;
  -- numeric_std: u = 256 is always FALSE; expected PROVED
  p1: assert not (u = big);
  -- u /= 256 always true
  p2: assert u /= big;
end architecture;
