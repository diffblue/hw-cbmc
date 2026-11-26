-- IEEE 1076-2008 5.2.2.1: enumeration literals may be overloaded;
-- the type is determined by the context
entity overloaded_literal1 is
  port(clk : in bit; y : out boolean);
end;
architecture rtl of overloaded_literal1 is
  type s1 is (idle, run);
  type s2 is (idle, stop);
  signal a : s1 := idle;
  signal b : s2 := idle;
begin
  process(clk)
  begin
    case b is
      when idle => a <= run;
      when stop => a <= idle;
    end case;
  end process;
  y <= a = idle and b = idle;
  p1: assert b = idle;
end;
