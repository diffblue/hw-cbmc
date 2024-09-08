class data;
  // rand bit [15:0] field1;
  constraint c_f1 {
    field1 dist {[0:31] :/ 1, [32:65535] :/ 1};
  }
endclass
