function int myfunc();
  // 1800-2017 13.4.1
  // "It shall also be illegal to declare another object with the same
  // name as the function inside the function scope."
  int myfunc;
  myfunc = 123;
endfunction
