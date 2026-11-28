-- IEEE 1076-2008 11.8: a generate statement body may have a declarative
-- part, followed by begin; found in PoC and in the GHDL synth tests
library ieee;
use ieee.std_logic_1164.all;
entity generate_declarations1 is
  port(a, b : in std_logic; y : out std_logic);
end;
architecture rtl of generate_declarations1 is
  constant USE_CARRY : boolean := true;
begin
  gen: if USE_CARRY generate
    signal carry : std_logic;
  begin
    carry <= a and b;
    y <= carry;
  end generate;
end;
