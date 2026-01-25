default: test

TEST_PL = ../../lib/cbmc/regression/test.pl

test:
	@$(TEST_PL) -e -p -c ../../../src/ebmc/ebmc -X buechi

test-buechi:
	@$(TEST_PL) -e -p -c ../../../src/ebmc/ebmc -I buechi

test-z3:
	@$(TEST_PL) -e -p -c "../../../src/ebmc/ebmc --z3" -X broken-smt-backend -X buechi

test-aig:
	@$(TEST_PL) -e -p -c "../../../src/ebmc/ebmc --aig" -X buechi
