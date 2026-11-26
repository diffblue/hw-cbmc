-- Counter over an integer subtype, clocked with rising_edge on std_logic,
-- with a synchronous reset.

library ieee;
use ieee.std_logic_1164.all;

entity counter1 is
  port(
    clk   : in  std_logic;
    reset : in  std_logic;
    count : out integer range 0 to 15);
end counter1;

architecture rtl of counter1 is

  signal cnt : integer range 0 to 15 := 0;

begin

  process(clk)
  begin
    if rising_edge(clk) then
      if reset = '1' then
        cnt <= 0;
      elsif cnt = 15 then
        cnt <= 0;
      else
        cnt <= cnt + 1;
      end if;
    end if;
  end process;

  count <= cnt;

  p1: assert cnt <= 15;
  p2: assert cnt /= 3;

end rtl;
