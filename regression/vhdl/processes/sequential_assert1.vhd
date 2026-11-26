-- Sequential assertion statements inside a clocked process, with
-- report and severity clauses. The assertion is checked in the
-- states in which the process body runs.

library ieee;
use ieee.std_logic_1164.all;

entity sequential_assert1 is
  port(
    clk : in  std_logic;
    inc : in  std_logic);
end sequential_assert1;

architecture rtl of sequential_assert1 is

  signal cnt : integer range 0 to 3 := 0;

begin

  process(clk)
  begin
    if rising_edge(clk) then
      if inc = '1' and cnt /= 3 then
        cnt <= cnt + 1;
      end if;

      p1: assert cnt <= 3
        report "counter out of range"
        severity failure;

      p2: assert cnt /= 2
        report "counter reached two"
        severity error;
    end if;
  end process;

end rtl;
