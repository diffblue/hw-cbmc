entity report_expr is
  port(a : in bit);
end;
architecture rtl of report_expr is
begin
  p1: assert a = '1' report "a" & "b";
end;
