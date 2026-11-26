-- IEEE 1076-2008 9.2.9: the implicit condition operator ??
library ieee;
use ieee.std_logic_1164.all;
entity if_std_logic1 is
  port(a : in std_logic; b : in bit; y, z : out bit);
end;
architecture rtl of if_std_logic1 is
begin
  process(a, b)
  begin
    if a then y <= '1'; else y <= '0'; end if;
    if b and '1' then z <= '1'; else z <= '0'; end if;
  end process;
  p1: assert (y = '1') = (a = '1');
  p2: assert z = b;
  p3: assert a or not a;
end;
