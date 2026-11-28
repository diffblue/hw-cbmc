-- IEEE 1076-2008 9.2.2: the logical operators are unary reduction
-- operators on arrays, e.g. and v, or v, xor v
library ieee;
use ieee.std_logic_1164.all;
entity reduction_operators1 is
  port(v : in std_logic_vector(3 downto 0); all_ones, any, parity : out std_logic);
end;
architecture rtl of reduction_operators1 is
begin
  all_ones <= and v;
  any <= or v;
  parity <= xor v;
end;
