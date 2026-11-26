library ieee;
use ieee.std_logic_1164.all;

entity unaffected1 is
  port (clk : in std_logic; d : in std_logic);
end entity;

architecture rtl of unaffected1 is
  signal q : std_logic := '0';
  signal u : std_logic := '1';
begin
  u <= unaffected;
  q <= d when rising_edge(clk);
  p0: assert u = '1';
end architecture;
