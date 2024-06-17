// run all defined tests for the AlgebraicTorus package

AttachSpec("main.spec");
SetAssertions(3);
SetDebugOnError(true);
SetNthreads(30);

import "_tests/unit_tests.m" : run_all_unit_tests;
import "_tests/integrated_tests.m" : run_all_integrated_tests;
import "_tests/fuzzing_tests.m" : run_all_fuzzing_tests;

print("\n");
print("================================");
print("I am now running all unit tests.");
print("================================");
run_all_unit_tests();

print("\n");
print("======================================");
print("I am now running all integrated tests.");
print("======================================");
run_all_integrated_tests();

print("\n");
print("===================================");
print("I am now running all fuzzing tests.");
print("===================================");
run_all_fuzzing_tests();

exit;
