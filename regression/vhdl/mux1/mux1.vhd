-- Concurrent signal assignments: conditional (when/else) and
-- selected (with/select).

library ieee;
use ieee.std_logic_1164.all;

entity mux1 is
  port(
    sel : in  std_logic_vector(1 downto 0);
    a   : in  std_logic;
    b   : in  std_logic;
    c   : in  std_logic;
    d   : in  std_logic;
    y   : out std_logic;
    z   : out std_logic);
end mux1;

architecture rtl of mux1 is

  signal y_int : std_logic;
  signal z_int : std_logic;

begin

  y_int <= a when sel = "00" else
           b when sel = "01" else
           c when sel = "10" else
           d;

  with sel select
    z_int <= a when "00",
             b when "01",
             c when "10",
             d when others;

  y <= y_int;
  z <= z_int;

  -- both encodings agree
  p1: assert y_int = z_int;

  -- and the output is not constant
  p2: assert y_int = a;

end rtl;
