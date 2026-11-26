-- IEEE 1076-2008 12.3: enumeration literals are overloadable, and
-- a literal declared in an inner region does not hide a homograph
-- declared in an enclosing region
entity literal_overload1 is
  port(clk : in bit; y : out boolean);
end;
architecture rtl of literal_overload1 is
  type color is (red, green, blue);
  signal c : color := red;
begin
  process(clk)
    type light is (red, yellow);
    variable l : light := red;
  begin
    if clk = '1' then
      l := yellow;
      c <= red;
      if l = yellow and c = red then
        c <= green;
      end if;
    end if;
  end process;
  y <= c = red;
  p1: assert c = red or c = green;
  p2: assert y = (c = red);
end;
