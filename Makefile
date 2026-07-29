CORE_SRCS=core.cpp lexer.cpp syntax.cpp
CORE_TEST_SRC=test_core.cpp
CORE_TEST_SRCS=$(CORE_SRCS) $(CORE_TEST_SRC)
UTIL_SRCS=$(CORE_SRCS) matcher.cpp unifier.cpp
UTIL_TEST_SRC=test_util.cpp
UTIL_TEST_SRCS=$(UTIL_SRCS) $(UTIL_TEST_SRC)
THEORY_SRCS=$(UTIL_SRCS) order.cpp theory.cpp
MAIN_SRC=inference.cpp rewrite.cpp definer.cpp parser.cpp main.cpp
MAIN_SRCS=$(THEORY_SRCS) $(MAIN_SRC)
SRCS=$(MAIN_SRCS) $(CORE_TEST_SRC) $(UTIL_TEST_SRC) $(THEORY_TEST_SRC)
CPP=g++ -std=c++20 -Wfatal-errors
DEPEND=_depend
BUILD=_build
DEBUG=_debug
SANITIZE=_sanitize
DEPS=$(SRCS:%.cpp=$(DEPEND)/%.d)
OBJS=$(SRCS:%.cpp=$(BUILD)/%.o)
DOBJS=$(SRCS:%.cpp=$(DEBUG)/%.o)
BUILD_CPP=$(CPP) -O3
DEBUG_CPP=$(CPP) -O0 -ggdb3 -fsanitize=address,alignment,undefined -fno-omit-frame-pointer
SANITIZE_CPP=$(CPP) -O1 -ggdb3 -fsanitize=address,alignment,undefined -fno-omit-frame-pointer
TGT=nlt
DEBUG_TGT=debug
SANITIZE_TGT=sanitize

.PHONY: core_test util_test

$(TGT): $(MAIN_SRCS:%.cpp=$(BUILD)/%.o)
	${BUILD_CPP} $^ -o $@

$(SANITIZE_TGT): $(MAIN_SRCS:%.cpp=$(SANITIZE)/%.o)
	${SANITIZE_CPP} $^ -o $@

$(DEBUG_TGT): $(MAIN_SRCS:%.cpp=$(DEBUG)/%.o)
	${DEBUG_CPP} $^ -o $@

run: $(TGT) test.nl
	$(TGT) test.nl

test_core.exe: $(CORE_TEST_SRCS:%.cpp=$(DEBUG)/%.o)
	${DEBUG_CPP} $^ -o $@

test_core: test_core.exe
	./$^

test_util.exe: $(UTIL_TEST_SRCS:%.cpp=$(DEBUG)/%.o)
	${DEBUG_CPP} $^ -o $@

test_util: test_util.exe
	./$^

.PHONY: vscode

vscode: vscode/language-configuration.json vscode/nlt.tmLanguage.json
	cd vscode; npx vsce package

$(DEPEND)/%.d: %.cpp
	@mkdir -p $(@D)
	${CPP} -MM $< > $@.base
	(echo -n $(BUILD)/; cat $@.base) > $@
	(echo -n $(DEBUG)/; cat $@.base) >> $@

$(BUILD)/%.o: %.cpp
	@mkdir -p $(@D)
	${BUILD_CPP} -c $< -o $@

$(DEBUG)/%.o: %.cpp
	@mkdir -p $(@D)
	${DEBUG_CPP} -c $< -o $@

$(SANITIZE)/%.o: %.cpp
	@mkdir -p $(@D)
	${SANITIZE_CPP} -c $< -o $@

.PHONY: clean test test_core test_util test_locale

clean:
	rm -rf $(DEPEND) $(BUILD) $(DEBUG) $(SANITIZE) $(TGT) $(DEBUG_TGT) $(SANITIZE_TGT)

-include ${DEPS}
