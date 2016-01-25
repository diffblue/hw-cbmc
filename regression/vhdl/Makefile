default: tests.log

test:
	@../test.pl -c ../../../src/ebmc/ebmc

tests.log: ../test.pl ../../../src/ebmc/ebmc
	@../test.pl

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
