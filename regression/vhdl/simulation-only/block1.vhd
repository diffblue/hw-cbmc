library ieee;
use ieee.std_logic_1164.all;
-- IEEE 1076-2008 11.2: a block without a guard is synthesised
entity block1 is port(clk, a : in std_logic; y : out std_logic); end;
architecture rtl of block1 is
  signal s : std_logic;
begin
  b: block
    signal t : std_logic;
  begin
    t <= a;
    s <= t;
  end block;
  y <= s;
  p1: assert y = a;
end;
