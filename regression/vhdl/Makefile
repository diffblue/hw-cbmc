default: tests.log

TEST_PL = ../../lib/cbmc/regression/test.pl

test:
	@$(TEST_PL) -e -p -c ../../../src/ebmc/ebmc

tests.log:
	@$(TEST_PL) -e -p -c ../../../src/ebmc/ebmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
