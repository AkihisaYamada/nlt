SRCS=core.cpp util.cpp unifier.cpp lexer.cpp syntax.cpp prover.cpp
CPP=g++ -ggdb -std=c++20 -Wfatal-errors
BUILD=_build
OBJS=$(SRCS:%.cpp=$(BUILD)/%.o)
DEPS=$(OBJS:%.o=%.d)

test.exe: ${OBJS}
	${CPP} $^ -o $@

test: test.exe proofscript
	./test.exe < proofscript

$(BUILD)/%.d: %.cpp
	@mkdir -p $(@D)
	(echo -n $(BUILD)/; ${CPP} -MM $<) > $@

$(BUILD)/%.o: %.cpp
	${CPP} -c $< -o $@

.PHONY: clean test

clean:
	rm -rf $(BUILD)

-include ${DEPS}
