SRCS=core.cpp util.cpp unifier.cpp lexer.cpp syntax.cpp rewriter.cpp definer.cpp prover.cpp
CPP=g++ -O3 -std=c++20 -Wfatal-errors
DEPEND=_depend
BUILD=_build
DEBUG=_debug
DEPS=$(SRCS:%.cpp=$(DEPEND)/%.d)
OBJS=$(SRCS:%.cpp=$(BUILD)/%.o)
DOBJS=$(SRCS:%.cpp=$(DEBUG)/%.o)
DCPP=g++ -O0 -ggdb3 -std=c++20 -Wfatal-errors

test.exe: ${DOBJS}
	${DCPP} $^ -o $@

nlm.exe: ${OBJS}
	${CPP} $^ -o $@

test: test.exe proofscript
	./test.exe proofscript

$(DEPEND)/%.d: %.cpp
	@mkdir -p $(@D)
	${CPP} -MM $< > $@.base
	(echo -n $(BUILD)/; cat $@.base) > $@
	(echo -n $(DEBUG)/; cat $@.base) >> $@

$(BUILD)/%.o: %.cpp
	@mkdir -p $(@D)
	${CPP} -c $< -o $@

$(DEBUG)/%.o: %.cpp
	@mkdir -p $(@D)
	${DCPP} -c $< -o $@

.PHONY: clean test

clean:
	rm -rf $(DEPEND) $(BUILD) $(DEBUG)

-include ${DEPS}
