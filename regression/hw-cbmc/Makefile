default: tests.log

test:
	@../test.pl -c ../../../src/hw-cbmc/hw-cbmc

tests.log: ../test.pl
	@../test.pl -c ../../../src/hw-cbmc/hw-cbmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
