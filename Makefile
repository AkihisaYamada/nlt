OBJS=core.o theories.o test.o
CPP=g++ -g -std=c++20

test.exe: ${OBJS}
	${CPP} $^ -o $@

%.o: %.cpp
	${CPP} -c $<

.PHONY: clean

clean:
	rm -rf ${OBJS}
