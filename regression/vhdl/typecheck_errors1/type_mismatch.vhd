entity type_mismatch is
  port(a : in bit; b : out boolean);
end type_mismatch;

architecture rtl of type_mismatch is
begin
  b <= a;
end rtl;
