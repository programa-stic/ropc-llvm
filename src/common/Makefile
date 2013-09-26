inc_dir		:= $(bap_lib_dir)

inc_params	:= $(foreach d,$(inc_dir),-I $d)

sources		:= 	common.ml \
				int_utils.ml
objects		:= $(subst .ml,.cmo,$(sources))

all: $(objects)

%.cmo: %.ml
	ocamlc -c $(inc_params) $<

clean:
	rm -f *.o *.cmo *.cmi  *.cmx
