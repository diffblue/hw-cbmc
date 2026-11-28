library ieee;
use ieee.std_logic_1164.all;
entity physical1 is port(clk, a : in std_logic); end;
architecture rtl of physical1 is
  signal s : std_logic;
begin
  s <= a after 5 ns;
end;
