-- Shift register over std_logic_vector: slicing, indexing, concatenation,
-- and a bit-string literal.

library ieee;
use ieee.std_logic_1164.all;

entity shift_register1 is
  port(
    clk  : in  std_logic;
    din  : in  std_logic;
    dout : out std_logic);
end shift_register1;

architecture rtl of shift_register1 is

  signal sr : std_logic_vector(7 downto 0) := "00000000";

begin

  process(clk)
  begin
    if rising_edge(clk) then
      sr <= sr(6 downto 0) & din;
    end if;
  end process;

  dout <= sr(7);

  -- the top bit stays zero for the first eight cycles
  p1: assert sr(7) = '0';

  -- the top two bits do not; bit 6 is reached after seven cycles
  p2: assert sr(7 downto 6) = "00";

end rtl;
