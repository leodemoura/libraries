LEAN = lean
LEAN_FILES = $(wildcard *.lean)
OLEAN_FILES = $(LEAN_FILES:.lean=.olean)
DEPS = make.deps

all: $(OLEAN_FILES) $(DEPS)

%.olean: %.lean
	$(LEAN) $< -n -o $@

clean:
	-rm *.olean $(DEPS)

$(DEPS): $(LEAN_FILES)
	./extract_deps $(LEAN_FILES) > make.deps

include $(DEPS)
