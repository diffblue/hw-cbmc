-- Process variables: immediate (:=) versus signal (<=) assignment
-- semantics within one clocked process.

library ieee;
use ieee.std_logic_1164.all;

entity variable1 is
  port(
    clk : in  std_logic;
    a   : in  integer range 0 to 7;
    s   : out integer range 0 to 15);
end variable1;

architecture rtl of variable1 is

  signal s_int : integer range 0 to 15 := 0;
  signal t     : integer range 0 to 7 := 0;

begin

  process(clk)
    variable tmp : integer range 0 to 15;
  begin
    if rising_edge(clk) then
      tmp := a;
      tmp := tmp + a;   -- variable sees the new value immediately
      s_int <= tmp;
      t <= a;
    end if;
  end process;

  s <= s_int;

  -- s_int is twice the previous input, and thus even
  p1: assert s_int = 2 * t;
  p2: assert s_int = 0;

end rtl;
