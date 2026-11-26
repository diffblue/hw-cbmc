library ieee;
use ieee.std_logic_1164.all;
entity wait1 is port(clk, a : in std_logic; y : out std_logic); end;
architecture rtl of wait1 is
begin
  process
  begin
    wait on clk until clk = '1' for 10 ns;
    y <= a;
  end process;
end;
