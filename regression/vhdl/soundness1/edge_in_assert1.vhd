library ieee;
use ieee.std_logic_1164.all;
-- a clock edge has no meaning in a property
entity edge_in_assert1 is port(clk : in std_logic); end;
architecture rtl of edge_in_assert1 is
begin
  p: assert rising_edge(clk) or not rising_edge(clk);
end;
