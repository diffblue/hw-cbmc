default: tests.log

test:
	@../test.pl -c hw-cbmc

tests.log: ../test.pl
	@../test.pl -c hw-cbmc

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
