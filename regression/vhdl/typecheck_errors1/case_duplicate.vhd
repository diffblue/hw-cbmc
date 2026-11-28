entity case_duplicate is
  port(a : in integer range 0 to 3; y : out bit);
end;
architecture rtl of case_duplicate is
begin
  process(a)
  begin
    case a is
      when 0 | 1 => y <= '0';
      when 1 to 3 => y <= '1';
    end case;
  end process;
end;
