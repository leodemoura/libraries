LEAN=lean
LEAN_FILES=$(wildcard *.lean)
OLEAN_FILES=$(LEAN_FILES:.lean=.olean)

all: $(OLEAN_FILES)

%.olean: %.lean
	$(LEAN) $< -o $@

clean:
	-rm $(OLEAN_FILES)
