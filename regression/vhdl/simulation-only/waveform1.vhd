library ieee;
use ieee.std_logic_1164.all;
entity waveform1 is port(clk, a : in std_logic); end;
architecture rtl of waveform1 is
  signal s : std_logic;
begin
  s <= a after 1 ns, clk after 2 ns;
end;
