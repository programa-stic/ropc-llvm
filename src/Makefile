bap_dir 	:= ../../lib/bap-0.4
bap_lib_dir := $(bap_dir)/ocaml
bin_dir		:= ../../bin
common_dir	:= ../common

deps		:= common
modules		:= gadget verify dumper compile

export bap_dir
export bap_lib_dir
export bin_dir
export common_dir

## Documentation
libasmir_dir	:= ../lib/bap-0.4/libasmir/src
pcre_dir		:= ../lib/bap-0.4/pcre-ocaml-release-6.2.2/lib

inc_dir			:= ../lib/bap-0.4/ocaml ../lib/bap-0.4/batteries-1.4.0/src/ $(pcre_dir) $(libasmir_dir) ./common $(modules)
inc_params		:= $(foreach d, $(inc_dir), -I $d)

sources			:= $(foreach dir, $(deps), $(wildcard $(dir)/*.ml))
sources			+= $(foreach dir, $(modules), $(wildcard $(dir)/*.ml))

packs			:= extlib,bigarray,str,ocamlgraph
ocaml_opts		:= -package $(packs)

.PHONY: all $(deps) $(modules) doc

all: $(deps) $(modules)

$(deps):
	$(MAKE) --directory=$@

$(modules): $(deps)
	$(MAKE) --directory=$@

doc: all
	ocamlfind ocamldoc $(ocaml_opts) -html $(inc_params) $(sources) -d ../doc/src -css-style ../doc/src/style.css

clean:
	$(MAKE) --directory=common clean
	$(MAKE) --directory=gadget clean
	$(MAKE) --directory=verify clean
	$(MAKE) --directory=compile clean
	$(MAKE) --directory=dumper clean

cleandoc:
	rm -f ../doc/src/*.html
