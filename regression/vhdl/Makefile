default: tests.log

test:
	@../test.pl -e -p -c ../../../src/ebmc/ebmc

tests.log:
	@../test.pl -e -p -c ../../../src/ebmc/ebmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
