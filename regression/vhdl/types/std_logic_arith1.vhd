-- Arithmetic with the Synopsys packages std_logic_arith and
-- std_logic_unsigned, as used by the ITC'99 b04 benchmark.

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

entity std_logic_arith1 is
  port(
    clk   : in  std_logic;
    reset : in  std_logic;
    data  : in  std_logic_vector(7 downto 0);
    max   : out std_logic_vector(7 downto 0));
end std_logic_arith1;

architecture rtl of std_logic_arith1 is

  signal max_reg : std_logic_vector(7 downto 0) := "00000000";

begin

  process(clk)
  begin
    if rising_edge(clk) then
      if reset = '1' then
        max_reg <= "00000000";
      elsif conv_integer(data) > conv_integer(max_reg) then
        max_reg <= data;
      end if;
    end if;
  end process;

  max <= max_reg;

  -- the maximum never decreases below the reset value
  p1: assert conv_integer(max_reg) >= 0;

  -- the maximum changes
  p2: assert max_reg = "00000000";

end rtl;
