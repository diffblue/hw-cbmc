entity case_nonstatic is
  port(a, b : in integer range 0 to 3; y : out bit);
end;
architecture rtl of case_nonstatic is
begin
  process(a, b)
  begin
    case a is
      when b => y <= '0';
      when others => y <= '1';
    end case;
  end process;
end;
