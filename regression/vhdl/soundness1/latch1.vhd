library ieee;
use ieee.std_logic_1164.all;

-- An incomplete assignment in a combinational process infers a latch
-- (IEEE 1076.6-2004 6.2.1.2), which holds its value when not enabled.
entity latch1 is port(en, d : in std_logic); end;
architecture rtl of latch1 is
  signal l : std_logic := '0';
  signal l_prev : std_logic := '0';
  signal was_enabled : std_logic := '0';
begin
  process(en, d) begin
    if en = '1' then l <= d; end if;
  end process;

  -- the latch is zero until it has been enabled
  p0: assert l = '0' or en = '1' or was_enabled = '1';
  -- and it does take values
  p1: assert l = '0';
end;
