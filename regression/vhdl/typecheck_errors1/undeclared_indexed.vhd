entity undeclared_indexed is
  port(y : out bit);
end;
architecture rtl of undeclared_indexed is
begin
  y <= c(0);
end;
