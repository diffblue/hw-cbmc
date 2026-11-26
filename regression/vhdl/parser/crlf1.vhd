-- FSM in the style of the ITC'99 b02 benchmark: a single clocked process
-- with an asynchronous reset, an integer-range state variable, and a
-- case statement.

entity crlf1 is
  port(
    reset : in bit;
    clock : in bit;
    linea : in bit;
    u     : out bit);
end crlf1;

architecture behav of crlf1 is

  constant A : integer := 0;
  constant B : integer := 1;
  constant C : integer := 2;
  constant D : integer := 3;
  constant E : integer := 4;

  signal stato : integer range 4 downto 0;

begin

  process(reset, clock)
  begin
    if reset = '1' then
      stato <= A;
      u <= '0';
    elsif clock'event and clock = '1' then
      case stato is
        when A =>
          stato <= B;
          u <= '0';
        when B =>
          if linea = '0' then
            stato <= C;
          else
            stato <= A;
          end if;
          u <= '0';
        when C =>
          stato <= D;
          u <= '0';
        when D =>
          stato <= E;
          u <= '1';
        when E =>
          stato <= A;
          u <= '0';
      end case;
    end if;
  end process;

  -- the range constraint is respected
  p1: assert stato <= 4;

  -- state D is reachable
  p2: assert stato /= 3;

end behav;
