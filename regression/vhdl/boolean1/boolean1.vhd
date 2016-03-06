library ieee;
use ieee.std_logic_1164.all;

entity boolean1_ent is
end boolean1_ent;  

architecture boolean1_test of boolean1_ent is 

signal a, b, c: boolean;

begin 

  process begin
    a:=true  or   false; assert a=true report "true or false";
    a:=false or   false; assert a=false report "false or false";
    a:=true  nor  false; assert a=false report "true nor false";
    a:=false nor  false; assert a=true report "false nor false";
    a:=true  and  false; assert a=false report "true and false";
    a:=true  and  true;  assert a=true report "true and true";
    a:=true  nand false; assert a=true report "true nand false";
    a:=true  nand true;  assert a=false report "true nand true";
    a:=true  xor  false; assert a=true report "true xor false";
    a:=true  xnor false; assert a=false report "true xnor false";
    a:=not false;        assert a=true report "not false";
  end process;

end boolean1_test;
