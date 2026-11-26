-- IEEE 1076-2008 16.8.2: for numeric_std "/" the result has the
-- length of the left operand, and for "rem" and "mod" the length of
-- the right operand
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity unsigned_div1 is
  port(a4 : in unsigned(3 downto 0); a8 : in unsigned(7 downto 0);
       b4 : in unsigned(3 downto 0);
       r4 : out unsigned(3 downto 0));
end;
architecture rtl of unsigned_div1 is
  constant c : unsigned(3 downto 0) := to_unsigned(9, 4);
  constant d : unsigned(7 downto 0) := to_unsigned(20, 8);
  constant c_div_d : unsigned := c / d;
  constant c_rem_d : unsigned := c rem d;
  constant c_mod_d : unsigned := c mod d;
  constant d_rem_c : unsigned := d rem c;
begin
  r4 <= a8 mod b4;
  p1: assert c_div_d = 0;
  p2: assert c_div_d'length = 4;
  p3: assert (c rem 20) = 9;
  p4: assert c_rem_d = 9;
  p5: assert c_rem_d'length = 8;
  p6: assert c_mod_d'length = 8;
  p7: assert (d / c) = 2;
  p8: assert d_rem_c = 2;
  p9: assert d_rem_c'length = 4;
  p10: assert r4 = a8 mod b4;
end;
