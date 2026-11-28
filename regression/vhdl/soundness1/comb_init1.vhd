-- The initial value in a declaration does not apply to a signal with a
-- combinational driver (IEEE 1076-2008 14.7.3.4); an incomplete assignment
-- in a combinational process infers a latch (IEEE 1076.6-2004 6.2.1.2).
library ieee;
use ieee.std_logic_1164.all;
entity comb_init1 is port(clk, a, en, d : in std_logic); end;
architecture rtl of comb_init1 is
  signal q : bit := '0';
  signal l : std_logic := '0';
begin
  q <= '1';                      -- P0: initializer must not contradict the driver
  p_false: assert q = '1';
  process(en, d) begin           -- latch
    if en = '1' then l <= d; end if;
  end process;
  p_latch: assert l = '0' or l = '1';
  p_vacuous: assert false;
end;
