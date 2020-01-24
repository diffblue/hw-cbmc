default: tests.log

include ../../lib/cbmc/src/config.inc
include ../../lib/cbmc/src/common

test:
	@../test.pl -c ../../../src/ebmc/ebmc

tests.log: ../test.pl
	@../test.pl

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
