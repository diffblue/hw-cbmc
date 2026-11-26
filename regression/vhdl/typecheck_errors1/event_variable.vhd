entity event_variable is
  port(clk : in bit; y : out bit);
end;
architecture rtl of event_variable is
begin
  process(clk)
    variable v : bit;
  begin
    if v'event then y <= '1'; end if;
  end process;
end;
