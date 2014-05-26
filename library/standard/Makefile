LEAN=lean
LEAN_FILES=$(wildcard *.lean)
OLEAN_FILES=$(LEAN_FILES:.lean=.olean)

all: 
	$(LEAN) $< -n -o kernel.olean kernel.lean -o nat.olean nat.lean -o list.olean list.lean

%.olean: %.lean
	$(LEAN) $< -n -o $@

clean:
	-rm $(OLEAN_FILES)
