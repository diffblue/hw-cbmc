-- IEEE 1076-2008 11.8: generate statements require a label
entity missing_label1 is end;
architecture a of missing_label1 is
begin
  for i in 0 to 1 generate end generate;
end;
