-- A user-defined array type (a small register bank, as in ITC'99 b05),
-- with a subtype for the index and an aggregate initialiser.

library ieee;
use ieee.std_logic_1164.all;

entity array1 is
  port(
    clk  : in  std_logic;
    we   : in  std_logic;
    addr : in  integer range 0 to 3;
    din  : in  std_logic_vector(3 downto 0);
    dout : out std_logic_vector(3 downto 0));
end array1;

architecture rtl of array1 is

  subtype word_t is std_logic_vector(3 downto 0);
  type bank_t is array (0 to 3) of word_t;

  signal bank : bank_t := (others => (others => '0'));

begin

  process(clk)
  begin
    if rising_edge(clk) then
      if we = '1' then
        bank(addr) <= din;
      end if;
    end if;
  end process;

  dout <= bank(addr);

  -- only one entry can be written per cycle
  p1: assert bank(0) = "0000" or bank(1) = "0000";
  p2: assert bank(0) = "0000";

end rtl;
