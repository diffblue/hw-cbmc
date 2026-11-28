library ieee;
use ieee.std_logic_1164.all;
entity disconnect1 is port(clk, a : in std_logic); end;
architecture rtl of disconnect1 is
  signal s : std_logic;
  disconnect s : std_logic after 5 ns;
begin
end;
