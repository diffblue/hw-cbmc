library ieee;
use ieee.std_logic_1164.all;
entity access_type1 is port(clk, a : in std_logic); end;
architecture rtl of access_type1 is
  type p is access integer;
begin
  process(clk)
    variable k : p;
  begin
    k := null;
  end process;
end;
