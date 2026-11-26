library ieee;
use ieee.std_logic_1164.all;
entity block_guard1 is port(clk, a, en : in std_logic; y : out std_logic); end;
architecture rtl of block_guard1 is
begin
  b: block(en = '1')
  begin
    y <= guarded a;
  end block;
end;
