default: tests.log

TEST_PL = ../../lib/cbmc/regression/test.pl

test:
	@$(TEST_PL) -e -p -c ../../../src/hw-cbmc/hw-cbmc

tests.log:
	@$(TEST_PL) -e -p -c ../../../src/hw-cbmc/hw-cbmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
