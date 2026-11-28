-- IEEE 1076-2008 12.3: a local declaration hides a declaration made
-- visible by a use clause
library ieee;
use ieee.std_logic_1164.all;
entity package_hidden1 is
  port(y : out boolean);
end;
architecture rtl of package_hidden1 is
  type std_logic is (lo, hi);
  signal s : std_logic := hi;
begin
  y <= s = hi;
  p1: assert y;
end;
