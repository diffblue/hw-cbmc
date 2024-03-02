module main(input clk);

  reg [7:0] seconds, minutes, hours;
  reg minute_tick, hour_tick, day_tick;

  wire second_tick = 1;

  initial begin
    seconds = 0;
    minutes = 0;
    hours = 0;
    day_tick = 0;
  end

  always @(posedge clk) begin
    minute_tick <= 0;
    hour_tick <= 0;
    day_tick <= 0;
    if(second_tick) begin
      if(seconds == 59) begin
        seconds <= 0;
        minute_tick <= 1;
        if(minutes == 59) begin
          minutes <= 0;
          hour_tick <= 1;
          if(hours == 23) begin
            hours <= 0;
            day_tick <= 1;
          end else
            hours <= hours + 1;
        end else
          minutes <= minutes + 1;
      end else
        seconds <= seconds + 1;
    end
  end

  // expected to pass
  p_minute: assert property (s_eventually minute_tick);
  p_hour: assert property (s_eventually hour_tick);
  p_day: assert property (s_eventually day_tick);

endmodule
