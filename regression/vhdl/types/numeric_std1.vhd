-- Arithmetic with ieee.numeric_std: unsigned counter, to_integer,
-- to_unsigned, and comparison against an integer.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity numeric_std1 is
  port(
    clk   : in  std_logic;
    reset : in  std_logic;
    count : out std_logic_vector(3 downto 0));
end numeric_std1;

architecture rtl of numeric_std1 is

  signal cnt : unsigned(3 downto 0) := (others => '0');

begin

  process(clk)
  begin
    if rising_edge(clk) then
      if reset = '1' then
        cnt <= to_unsigned(0, 4);
      else
        cnt <= cnt + 1;
      end if;
    end if;
  end process;

  count <= std_logic_vector(cnt);

  p1: assert to_integer(cnt) < 16;
  p2: assert cnt /= 2;

end rtl;
