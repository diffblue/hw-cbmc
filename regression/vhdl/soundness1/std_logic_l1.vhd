-- 'L' is a value of std_ulogic distinct from '0' (std_logic_1164);
-- the design is two-valued, so a comparison with 'L' is rejected
-- rather than read as '0'
library ieee;
use ieee.std_logic_1164.all;
entity std_logic_l1 is
  port(s : in std_logic; y : out boolean);
end;
architecture rtl of std_logic_l1 is
begin
  y <= s = 'L';
end;
