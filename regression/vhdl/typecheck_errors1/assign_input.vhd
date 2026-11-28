entity assign_input is
  port(a : in bit; b : out bit);
end assign_input;

architecture rtl of assign_input is
begin
  a <= b;
end rtl;
