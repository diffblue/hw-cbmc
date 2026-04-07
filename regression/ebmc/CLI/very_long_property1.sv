module main(input this_is_a_very_long_and_verbose_identifier);

  always_comb @this_is_a_very_long_and_verbose_identifier begin : blk
    a0: assert final(
        this_is_a_very_long_and_verbose_identifier
      + this_is_a_very_long_and_verbose_identifier
      + this_is_a_very_long_and_verbose_identifier
      + this_is_a_very_long_and_verbose_identifier
      + this_is_a_very_long_and_verbose_identifier
      != 5);
  end

endmodule;
