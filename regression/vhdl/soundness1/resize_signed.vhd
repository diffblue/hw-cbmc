library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity resize_signed is
  port (clk : in std_logic);
end entity;

architecture rtl of resize_signed is
  signal s : signed(7 downto 0) := "10000000"; -- -128
  signal r : signed(3 downto 0);
  signal u : std_logic := '0';
begin
  r <= resize(s, 4);
  -- numeric_std: sign bit kept, rightmost 3 bits: "1000" = -8
  p0: assert r = "1000";
end architecture;
