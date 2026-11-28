-- IEEE 1076-2008 9.2.5: concatenation of arrays and elements
library ieee;
use ieee.std_logic_1164.all;
entity concatenation1 is
  port(a : in std_logic_vector(3 downto 0); b : in std_logic;
       y : out std_logic_vector(4 downto 0); z : out std_logic_vector(5 downto 0);
       w : out std_logic_vector(1 downto 0));
end;
architecture rtl of concatenation1 is
begin
  y <= b & a;
  z <= a & "01";
  w <= '1' & '0';
  p1: assert y(4) = b and y(3 downto 0) = a;
  p2: assert z(5 downto 2) = a and z(1 downto 0) = "01";
  p3: assert w = "10";
end;
