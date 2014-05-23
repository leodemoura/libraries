LIB_DIRS = library/standard/ \
	     library/hott/

clean_LIBS=$(addprefix clean_,$(LIB_DIRS))

all: $(LIB_DIRS)
clean: $(clean_LIBS)

.PHONY: force

$(LIB_DIRS): force
	make -C $@

$(clean_LIBS): force
	make -C $(patsubst clean_%,%,$@) clean
