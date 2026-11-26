-- Generics: a parametrised counter width with a default value.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity generic1 is
  generic(
    WIDTH : natural := 3);
  port(
    clk   : in  std_logic;
    count : out std_logic_vector(WIDTH-1 downto 0));
end generic1;

architecture rtl of generic1 is

  signal cnt : unsigned(WIDTH-1 downto 0) := (others => '0');

begin

  process(clk)
  begin
    if rising_edge(clk) then
      cnt <= cnt + 1;
    end if;
  end process;

  count <= std_logic_vector(cnt);

  p1: assert cnt'length = WIDTH;
  p2: assert cnt /= 2**WIDTH - 1;

end rtl;
