library ieee;
use ieee.std_logic_1164.all;
entity aggregate_target1 is port(clk, a : in std_logic); end;
architecture rtl of aggregate_target1 is
  signal s, t : std_logic;
begin
  (s, t) <= "01";
end;
