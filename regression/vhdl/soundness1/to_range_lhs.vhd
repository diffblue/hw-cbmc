library ieee;
use ieee.std_logic_1164.all;

-- Assignments to a bit, a slice, and a bit with a non-constant index
-- of vectors with an increasing (to) range.
entity to_range_lhs is
  port (clk : in std_logic);
end entity;

architecture rtl of to_range_lhs is
  signal v   : std_logic_vector(0 to 3) := "0000";
  signal w   : std_logic_vector(0 to 3) := "0000";
  signal s   : std_logic_vector(0 to 7) := "00000000";
  signal idx : integer range 0 to 3 := 2;
begin
  process(clk)
  begin
    if rising_edge(clk) then
      v(0) <= '1';
      w(idx) <= '1';
      s(2 to 5) <= "1111";
    end if;
  end process;

  p0: assert v = "1000" or v = "0000";
  p1: assert v(0) = '1' or v = "0000";
  p2: assert w = "0010" or w = "0000";
  p3: assert s = "00111100" or s = "00000000";
  p4: assert s(2) = '1' or s = "00000000";
  -- the sanity check: the first bit does change
  p5: assert v(0) = '0';
end architecture;
