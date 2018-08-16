all: bin

# Configurable
DBGFLAGS ?= -g -O0 -DTEST
CPPFLAGS ?=
CFLAGS   ?= -Wall -Werror -Wpedantic $(DBGFLAGS)

# Source and output files
MAIN	:= vm
SRCS	:= vm.c
DEPDIR	:= .d

# Source and output files for test target
TEST	:= test
$(TEST):  $(patsubst %.c,%.o,$(SRCS) test.c); $(CC) -o $@ $^

# Handle header dependency. Huge thanks to the following article:
# http://make.mad-scientist.net/papers/advanced-auto-dependency-generation/
$(shell mkdir -p $(DEPDIR) >/dev/null)
DEPFLAGS    = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.Td
COMPILE.c   = $(CC) $(DEPFLAGS) $(CFLAGS) $(CPPFLAGS) $(TARGET_ARCH) -c
POSTCOMPILE = @mv -f $(DEPDIR)/$*.Td $(DEPDIR)/$*.d && touch $@

# How to compile each source file taking care of updating dependency
# files.
$(DEPDIR)/%.d:;
.PRECIOUS: $(DEPDIR)/%.d
%.o: %.c
%.o: %.c $(DEPDIR)/%.d
	$(COMPILE.c) $(OUTPUT_OPTION) $<
	$(POSTCOMPILE)

# Generate objects and main binary
bin: $(MAIN)
$(MAIN): $(patsubst %.c,%.o,$(SRCS) main.c); $(CC) -o $@ $^

# Get rid of garbage
clean:; -rm $(MAIN) $(TEST) *.o

# Include the dependency rules for each source file
include $(wildcard $(patsubst %,$(DEPDIR)/%.d,$(basename $(SRCS))))
