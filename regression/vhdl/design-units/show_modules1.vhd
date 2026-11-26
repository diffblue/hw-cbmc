entity show_modules1 is
end show_modules1;
architecture a of show_modules1 is
  signal x : boolean;
begin
  process begin
    assert x or not x report "tautology";
  end process;
end a;
