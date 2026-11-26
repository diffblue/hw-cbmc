entity overloaded_ambiguous is
  port(clk : in bit; y : out boolean);
end;
architecture rtl of overloaded_ambiguous is
  type s1 is (idle, run);
  type s2 is (idle, stop);
begin
  y <= idle = idle;
end;
