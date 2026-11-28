entity case_missing is
  port(a : in integer range 0 to 3; y : out bit);
end;
architecture rtl of case_missing is
begin
  process(a)
  begin
    case a is
      when 0 | 1 => y <= '0';
      when 2 => y <= '1';
    end case;
  end process;
end;
