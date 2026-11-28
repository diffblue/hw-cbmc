-- IEEE 1076-2008 12.3: a declaration in an inner declarative region
-- hides a homograph in an outer region
entity shadow1 is
  port(clk : in bit; y : out integer);
end;
architecture rtl of shadow1 is
  constant n : integer := 3;
begin
  process(clk)
    variable n : integer := 5;
  begin
    y <= n;
  end process;
  p1: assert y = 5;
end;
