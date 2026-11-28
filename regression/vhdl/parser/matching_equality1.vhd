-- IEEE 1076-2008 9.2.3: the matching relational operators ?= ?/= ?< ?<=
-- ?> ?>= on bit, std_ulogic and their vectors
library ieee;
use ieee.std_logic_1164.all;
entity matching_equality1 is
  port(a, b : in std_logic_vector(3 downto 0); eq, ne : out std_logic);
end;
architecture rtl of matching_equality1 is
begin
  eq <= a ?= b;
  ne <= a ?/= "1100";
end;
