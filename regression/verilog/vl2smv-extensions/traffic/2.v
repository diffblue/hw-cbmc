module main(N_SENSE,S_SENSE,E_SENSE,N_GO,S_GO,E_GO);

/*
 This program implements a traffic light controller.

 Input signals:
	N_SENSE -
            When this goes high, a car from the north is waiting to cross the
	    intersection.  (This signal does not have to remain high until
	    the request is granted.)  Once the request has been granted, this 
	    signal goes low to indicate that the car has finished crossing
	    the intersection.
	S_SENSE - Same as N, except for traffic from the south.
	E_SENSE - Same as N, except for traffic from the east.

 Output signals:
	N_GO - If this signal is high, traffic from the north is permitted to
	    enter the intersection.  If it is low, traffic must wait.
	S_GO - Same as N_GO, except for traffic from the south.
	E_GO - Same as N_GO, except for traffic from the east.

 Internal signals:
	N_REQ - Since N is not required to remain high to indicate that a
	    car from the north wants to cross the intersection, this signal
	    is used to latch requests from the north.
	S_REQ - Same as N_REQ, except for traffic from the south.
	E_REQ - Same as N_REQ, except for traffic from the east.
	NS_LOCK - This signal is set high by north/south traffic in order to
	    lock out traffic from the east.
	EW_LOCK - This signal is set high by east traffic in order to
	    lock out traffic from the north/south.
*/

  input  N_SENSE, S_SENSE, E_SENSE;
  output N_GO, S_GO, E_GO;

  wire   N_SENSE, S_SENSE, E_SENSE;
  reg    N_GO, S_GO, E_GO;
  reg    NS_LOCK, EW_LOCK, N_REQ, S_REQ, E_REQ;

  initial begin
    N_REQ = 0; S_REQ = 0; E_REQ = 0;
    N_GO = 0; S_GO = 0; E_GO = 0;
    NS_LOCK = 0; EW_LOCK = 0;
  end


/* latch traffic sensor inputs */

  always begin if (!N_REQ & N_SENSE) N_REQ = 1; end
  always begin if (!S_REQ & S_SENSE) S_REQ = 1; end
  always begin if (!E_REQ & E_SENSE) E_REQ = 1; end

/* North traffic controller */

  always begin
    if (N_REQ)
      begin
        wait (!EW_LOCK & !(S_GO & !S_SENSE));
        NS_LOCK = 1;
        N_GO = 1;
	wait (!N_SENSE);
        if (!S_GO) NS_LOCK = 0;
	N_GO = 0;
        N_REQ = 0;
      end
  end

/* South traffic controller */

  always begin
    if (S_REQ)
      begin
        wait (!EW_LOCK & !(N_GO & !N_SENSE));
        NS_LOCK = 1; S_GO = 1;
        wait (!S_SENSE);
        if (!N_GO) NS_LOCK = 0;
        S_GO = 0; S_REQ = 0;
      end
  end

/* East traffic controller */

  always begin
    if (E_REQ) 
      begin
        EW_LOCK = 1;
        wait (!NS_LOCK);
        E_GO = 1;
        wait (!E_SENSE);
        EW_LOCK = 0; E_GO = 0; E_REQ = 0;
      end
  end 

/* specifications */

always begin
  assert mutex: !(E_GO & (S_GO | N_GO));
  if (E_SENSE) assert E_live: eventually E_GO;
  if (S_SENSE) assert S_live: eventually S_GO;
  if (N_SENSE) assert N_live: eventually N_GO;
end

/* assumptions */

always begin
  assert E_fair: eventually !(E_GO & E_SENSE);
  assert S_fair: eventually !(S_GO & S_SENSE);
  assert N_fair: eventually !(N_GO & N_SENSE);
end

using E_fair, S_fair, N_fair  prove   E_live, S_live, N_live;
assume E_fair, S_fair, N_fair;


endmodule