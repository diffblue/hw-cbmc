default: tests.log

test:
	@../test.pl -e -p -c ../../../src/hw-cbmc/hw-cbmc

tests.log:
	@../test.pl -e -p -c ../../../src/hw-cbmc/hw-cbmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
