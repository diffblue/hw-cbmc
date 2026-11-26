-- A pure function declared in the architecture declarative part.

library ieee;
use ieee.std_logic_1164.all;

entity function1 is
  port(
    a : in  std_logic_vector(3 downto 0);
    p : out std_logic);
end function1;

architecture rtl of function1 is

  function parity(v : std_logic_vector) return std_logic is
    variable result : std_logic := '0';
  begin
    for i in v'range loop
      result := result xor v(i);
    end loop;
    return result;
  end function;

  signal p_int : std_logic;

begin

  p_int <= parity(a);
  p <= p_int;

  p1: assert p_int = (a(0) xor a(1) xor a(2) xor a(3));
  p2: assert p_int = '0';

end rtl;
