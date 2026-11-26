library ieee;
use ieee.std_logic_1164.all;

entity multi_driver is
  port (clk : in std_logic; a, b : in std_logic);
end entity;

architecture rtl of multi_driver is
  signal q : std_logic := '0';
begin
  p_a: process(clk)
  begin
    if rising_edge(clk) then q <= a; end if;
  end process;
  p_b: process(clk)
  begin
    if rising_edge(clk) then q <= b; end if;
  end process;
  -- should be a conversion error (multiple drivers), not a vacuous PROVED
  p0: assert q = '0';
end architecture;
