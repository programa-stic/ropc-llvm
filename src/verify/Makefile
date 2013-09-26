libasmir_dir	:= $(bap_dir)/libasmir/src
pcre_dir		:= $(bap_dir)/pcre-ocaml-release-6.2.2/lib
inc_dir			:= $(bap_lib_dir) $(pcre_dir) $(libasmir_dir) $(common_dir)

inc_params		:= $(foreach d, $(inc_dir), -I $d)

libs 			:= $(libasmir_dir)/libasmir.a $(bap_lib_dir)/bap.cma
deps 			:= $(common_dir)/common.cmo $(common_dir)/int_utils.cmo
sources			:= verify.ml
objects			:= $(subst .ml,.cmo,$(sources))

packs			:= bigarray,str,num,unix,ocamlgraph,camomile,threads
ocaml_opts		:= -package $(packs) -linkpkg -thread

all: verify

verify: $(objects)
	ocamlfind ocamlc $(ocaml_opts) $(inc_params) $(libs) $(deps) $(objects) -o $@
	mv $@ $(bin_dir)/$@-bap-0.4

%.cmo: %.ml
	ocamlc -c -I $(common_dir) $(inc_params) $<

clean:
	rm -f *.o *.cmo *.cmi
	rm -f $(bin_dir)/verify-bap-0.4