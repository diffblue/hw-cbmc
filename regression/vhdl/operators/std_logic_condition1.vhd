-- IEEE 1076-2008 9.2.9: a std_ulogic condition is converted with the
-- implicit ?? operator, which treats 'H' as true and 'L' as false
library ieee;
use ieee.std_logic_1164.all;
entity std_logic_condition1 is
  port(clk : in std_logic; s : in std_logic; y : out std_logic);
end;
architecture rtl of std_logic_condition1 is
  constant h : std_logic := 'H';
  constant l : std_logic := 'L';
begin
  process(clk)
  begin
    if clk = '1' then
      if s then
        y <= '1';
      else
        y <= '0';
      end if;
    end if;
  end process;
  p1: assert h;
  p2: assert not (?? l);
  p3: assert ?? h;
  p4: assert (?? l) = false;
end;
