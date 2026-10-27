// Classes with value parameters that have no default
// (sv-tests generic/class/class_test_9, class_test_26).
class Foo #(int N);
endclass

interface class Bar #(parameter N);
endclass

module main;
endmodule
