-- IEEE 1076.6-2004 6.1.3.1: a clocked process is a single if statement
library ieee;
use ieee.std_logic_1164.all;
entity mixed_timing1 is port(clk, a : in std_logic); end;
architecture rtl of mixed_timing1 is
  signal q, r : std_logic := '0';
begin
  process(clk, a) begin
    q <= a;
    if rising_edge(clk) then r <= a; end if;
  end process;
  p: assert q = r;
end;
