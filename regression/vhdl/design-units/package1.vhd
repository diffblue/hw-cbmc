-- A user-defined package providing a constant and a subtype, used by
-- the design through a use clause.

library ieee;
use ieee.std_logic_1164.all;

package defs is
  constant MAX : integer := 5;
  subtype cnt_t is integer range 0 to MAX;
end package;

library ieee;
use ieee.std_logic_1164.all;
use work.defs.all;

entity package1 is
  port(
    clk : in  std_logic;
    cnt : out cnt_t);
end package1;

architecture rtl of package1 is

  signal cnt_int : cnt_t := 0;

begin

  process(clk)
  begin
    if rising_edge(clk) then
      if cnt_int = MAX then
        cnt_int <= 0;
      else
        cnt_int <= cnt_int + 1;
      end if;
    end if;
  end process;

  cnt <= cnt_int;

  p1: assert cnt_int <= MAX;
  p2: assert cnt_int /= MAX;

end rtl;
