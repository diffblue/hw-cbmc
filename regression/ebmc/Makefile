default: test

TEST_PL = ../../lib/cbmc/regression/test.pl

test:
	@$(TEST_PL) -c ../../../src/ebmc/ebmc

test-z3:
	@$(TEST_PL) -e -p -c "../../../src/ebmc/ebmc --z3" -X broken-smt-backend
