entity entity1 is
end entity1;
architecture a of entity1 is
  signal x : boolean;
begin
  process begin
    assert x or not x report "tautology";
  end process;
end a;
