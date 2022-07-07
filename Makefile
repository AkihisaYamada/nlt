OBJS=core.o theories.o test.o
CPP=g++ -g -std=c++20
DEPS=$(OBJS:%.o=%.d)

test.exe: ${OBJS}
	${CPP} $^ -o $@

%.d: %.cpp
	${CPP} -MM $< > $@

%.o: %.cpp
	${CPP} -c $<

.PHONY: clean

clean:
	rm -rf ${OBJS} ${DEPS}

-include ${DEPS}
