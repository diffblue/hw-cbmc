library ieee;
use ieee.std_logic_1164.all;

entity sla1 is
  port (v : in bit_vector(3 downto 0); w : out bit_vector(3 downto 0));
end entity;

architecture rtl of sla1 is
begin
  -- IEEE 1076-2008 9.2.8: sla fills with the right-most element;
  -- this is not supported
  w <= v sla 1;
end architecture;
