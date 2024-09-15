CORE_SRCS=core.cpp lexer.cpp syntax.cpp debug.cpp
CORE_TEST_SRC=test/core_test.cpp
CORE_TEST_SRCS=$(CORE_SRCS) $(CORE_TEST_SRC)
UTIL_SRCS=$(CORE_SRCS) util.cpp unifier.cpp
UTIL_TEST_SRC=test/util_test.cpp
UTIL_TEST_SRCS=$(UTIL_SRCS) $(UTIL_TEST_SRC)
PROVER_SRC=rewriter.cpp definer.cpp prover.cpp
PROVER_SRCS=$(UTIL_SRCS) $(PROVER_SRC)
SRCS=$(PROVER_SRCS) $(CORE_TEST_SRC) $(UTIL_TEST_SRC)
CPP=g++ -O3 -std=c++20 -Wfatal-errors
DEPEND=_depend
BUILD=_build
DEBUG=_debug
DEPS=$(SRCS:%.cpp=$(DEPEND)/%.d)
OBJS=$(SRCS:%.cpp=$(BUILD)/%.o)
DOBJS=$(SRCS:%.cpp=$(DEBUG)/%.o)
DCPP=g++ -O0 -ggdb3 -std=c++20 -Wfatal-errors

.PHONY: core_test util_test

core_test.exe: $(TEST_SRCS:%.cpp=$(DEBUG)/%.o)
	${DCPP} $^ -o $@

core_test: core_test.exe
	./$@

util_test.exe: $(UTIL_TEST_SRCS:%/cpp=$(DEBUG)/%.o)
	${DCPP} $^ -o $@

util_test: util_test.exe
	./$@

nlm.exe: $(PROVER_SRCS:$(BUILD)/%.o)
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
