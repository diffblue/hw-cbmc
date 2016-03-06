library ieee;
use ieee.std_logic_1164.all;

entity std_logic1_ent is
end std_logic1_ent;  

architecture std_logic1_test of std_logic1_ent is 

signal a, b, c: std_logic;

begin 

  process begin
    a:='1' or   '0'; assert a='1' report "1 or 0";
    a:='0' or   '0'; assert a='0' report "0 or 0";
    a:='1' nor  '0'; assert a='0' report "1 nor 0";
    a:='0' nor  '0'; assert a='1' report "0 nor 0";
    a:='1' and  '0'; assert a='0' report "1 and 0";
    a:='1' and  '1'; assert a='1' report "1 and 1";
    a:='1' nand '0'; assert a='1' report "1 nand 0";
    a:='1' nand '1'; assert a='0' report "1 nand 1";
    a:='1' xor  '0'; assert a='1' report "1 xor 0";
    a:='1' xnor '0'; assert a='0' report "1 xnor 0";
    a:=not '0';      assert a='1' report "not 0";
  end process;

end std_logic1_test;
