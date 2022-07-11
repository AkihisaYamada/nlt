OBJS=core.o print.o theories.o prover.o lexer.o syntax.o
CPP=g++ -g -std=c++20 -Wfatal-errors
DEPS=$(OBJS:%.o=%.d)

test.exe: ${OBJS}
	${CPP} $^ -o $@

test: test.exe
	./test.exe

%.d: %.cpp
	${CPP} -MM $< > $@

%.o: %.cpp
	${CPP} -c $<

.PHONY: clean test

clean:
	rm -rf ${OBJS} ${DEPS}

-include ${DEPS}
