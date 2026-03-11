typedef union packed {
  bit array[4]; // error -- not packed
  bit [3:0] as_vector;
} u_t;
