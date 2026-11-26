library ieee;
use ieee.std_logic_1164.all;
entity time1 is port(clk, a : in std_logic); end;
architecture rtl of time1 is
  constant period : time := 10 ns;
begin
  -- IEEE 1076-2008 5.2.4: time is a physical type
  p: assert period / 2 = 5000 ps and 1.5 us > period * 100;
end;
