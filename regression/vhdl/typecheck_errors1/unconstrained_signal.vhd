-- IEEE 1076-2008 6.4.2.3: a signal must have a constrained subtype
entity unconstrained_signal is
  port(y : out bit);
end;
architecture rtl of unconstrained_signal is
  signal s : bit_vector;
begin
  y <= s(0);
end;
