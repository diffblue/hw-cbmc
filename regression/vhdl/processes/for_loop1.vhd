-- A for loop with a static range inside a clocked process, and a
-- process variable used as an accumulator.

library ieee;
use ieee.std_logic_1164.all;

entity for_loop1 is
  port(
    clk  : in  std_logic;
    v    : in  std_logic_vector(3 downto 0);
    ones : out integer range 0 to 4);
end for_loop1;

architecture rtl of for_loop1 is

  signal ones_int : integer range 0 to 4 := 0;

begin

  process(clk)
    variable count : integer range 0 to 4;
  begin
    if rising_edge(clk) then
      count := 0;
      for i in 0 to 3 loop
        if v(i) = '1' then
          count := count + 1;
        end if;
      end loop;
      ones_int <= count;
    end if;
  end process;

  ones <= ones_int;

  p1: assert ones_int <= 4;
  p2: assert ones_int /= 4;

end rtl;
