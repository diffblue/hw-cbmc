// Declarations of dynamic arrays (1800-2017 7.5)
// (sv-tests chapter-7/arrays/dynamic/basic).
module main;
  bit [7:0] arr[];
  int arr2[][];
  int arr3[][4];

  function int f(int a[]);
    return 0;
  endfunction
endmodule
