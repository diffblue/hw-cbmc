library ieee;
use ieee.std_logic_1164.all;
entity allocator1 is port(clk, a : in std_logic); end;
architecture rtl of allocator1 is
  type p is access integer;
  type r is record x : integer; end record;
  type rp is access r;
begin
  process(clk)
    variable k : p;
    variable q : rp;
  begin
    k := new integer;
    k.all := 1;
    q := new r;
    q.x := k.all;
  end process;
end;
