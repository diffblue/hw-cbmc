-- the constraint of a port of an unconstrained type comes from the
-- port map of an instantiation; the top-level entity has none
entity unconstrained_port is
  port(p : in bit_vector; y : out bit);
end;
architecture rtl of unconstrained_port is
begin
  y <= p(0);
end;
