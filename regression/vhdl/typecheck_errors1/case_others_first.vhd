entity case_others_first is
  port(a : in integer range 0 to 3; y : out bit);
end;
architecture rtl of case_others_first is
begin
  process(a)
  begin
    case a is
      when others => y <= '0';
      when 2 => y <= '1';
    end case;
  end process;
end;
