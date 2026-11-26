-- IEEE 1076-2008 5.3.3 permits record elements of an unconstrained
-- type, constrained by the object; this is not supported
library ieee;
use ieee.std_logic_1164.all;
entity record_unconstrained is
end;
architecture rtl of record_unconstrained is
  type t_rec is record
    elem : std_logic_vector;
  end record;
begin
  p1: assert t_rec'(elem => "000") = t_rec'(elem => "000");
end;
