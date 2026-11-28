library ieee;
use ieee.std_logic_1164.all;
entity resolution1 is port(clk, a : in std_logic); end;
architecture rtl of resolution1 is
  -- the resolution function would come from a package
  signal s : resolved std_logic;
begin
end;
