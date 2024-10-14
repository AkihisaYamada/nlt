CORE_SRCS=core.cpp lexer.cpp syntax.cpp debug.cpp
CORE_TEST_SRC=test_core.cpp
CORE_TEST_SRCS=$(CORE_SRCS) $(CORE_TEST_SRC)
UTIL_SRCS=$(CORE_SRCS) matcher.cpp unifier.cpp
UTIL_TEST_SRC=test_util.cpp
UTIL_TEST_SRCS=$(UTIL_SRCS) $(UTIL_TEST_SRC)
LOCALE_SRCS=$(UTIL_SRCS) locale.cpp
LOCALE_TEST_SRC=test_locale.cpp
LOCALE_TEST_SRCS=$(LOCALE_SRCS) $(LOCALE_TEST_SRC)
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

test_core.exe: $(CORE_TEST_SRCS:%.cpp=$(DEBUG)/%.o)
	${DCPP} $^ -o $@

test_core: test_core.exe
	./$^

test_util.exe: $(UTIL_TEST_SRCS:%.cpp=$(DEBUG)/%.o)
	${DCPP} $^ -o $@

test_util: test_util.exe
	./$^

test_locale.exe: $(LOCALE_TEST_SRCS:%.cpp=$(DEBUG)/%.o)
	${DCPP} $^ -o $@

test_locale: test_locale.exe
	./$^

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

.PHONY: clean test test_core test_util test_locale

clean:
	rm -rf $(DEPEND) $(BUILD) $(DEBUG)

-include ${DEPS}
