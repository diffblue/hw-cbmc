library ieee;
use ieee.std_logic_1164.all;

entity edge_else is
  port (clk : in std_logic; d : in std_logic);
end entity;

architecture rtl of edge_else is
  signal q : std_logic := '0';
begin
  -- IEEE 1076.6-2004 6.1.3.1: no else branch on the clock edge
  process(clk)
  begin
    if rising_edge(clk) then
      q <= d;
    else
      q <= '0';
    end if;
  end process;
end architecture;
