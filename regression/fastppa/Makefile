default: test

TEST_PL = ../../lib/cbmc/regression/test.pl

test:
	@$(TEST_PL) -e -p -c ../../../src/fastppa/fastppa
	@python3 properties/check.py ../../src/fastppa/fastppa
