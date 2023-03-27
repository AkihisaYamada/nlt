SRCS=core.cpp util.cpp unifier.cpp lexer.cpp syntax.cpp rewriter.cpp definer.cpp prover.cpp
CPP=g++ -O3 -std=c++20 -Wfatal-errors
BUILD=_build
OBJS=$(SRCS:%.cpp=$(BUILD)/%.o)
DEPS=$(OBJS:%.o=%.d)
DEBUG=_debug
DCPP=g++ -O0 -ggdb3 -std=c++20 -Wfatal-errors
DOBJS=$(SRCS:%.cpp=$(DEBUG)/%.o)

test.exe: ${DOBJS}
	${DCPP} $^ -o $@

nlm.exe: ${OBJS}
	${CPP} $^ -o $@

test: test.exe proofscript
	./test.exe proofscript

$(BUILD)/%.d: %.cpp
	@mkdir -p $(@D)
	(echo -n $(BUILD)/; ${CPP} -MM $<) > $@ || rm $@

$(BUILD)/%.o: %.cpp
	${CPP} -c $< -o $@

$(DEBUG)/%.o: %.cpp
	${DCPP} -c $< -o $@

.PHONY: clean test

clean:
	rm -rf $(BUILD) $(DEBUG)

-include ${DEPS}
