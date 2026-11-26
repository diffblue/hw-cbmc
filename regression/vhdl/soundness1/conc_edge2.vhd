library ieee;
use ieee.std_logic_1164.all;

entity conc_edge2 is
  port (clk : in std_logic; d : in std_logic);
end entity;

architecture rtl of conc_edge2 is
  signal q1 : std_logic := '0';
  signal q2 : std_logic := '0';
begin
  -- IEEE 1076.6-2004 6.1.3.3: clocked concurrent signal assignment;
  -- both are flip-flops with the same D input and clock
  q1 <= d when rising_edge(clk);
  q2 <= d when rising_edge(clk);
  p0: assert q1 = q2;  -- expected PROVED
end architecture;
