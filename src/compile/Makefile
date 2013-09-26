libasmir_dir	:= $(bap_dir)/libasmir/src
pcre_dir		:= $(bap_dir)/pcre-ocaml-release-6.2.2/lib
inc_dir			:= $(bap_lib_dir) $(pcre_dir) $(libasmir_dir) $(common_dir)

inc_params		:= $(foreach d,$(inc_dir),-I $d)

libs 			:= $(libasmir_dir)/libasmir.a $(bap_lib_dir)/bap.cma
deps			:= $(common_dir)/common.cmo
sources			:= 	roplAst.ml \
					roplParser.ml \
					roplLexer.ml \
					ssaForm.ml \
					regSets.ml \
					roplAstRewriter.ml \
					ssaFormPrinter.ml \
					analysis.ml \
					llvmAst.ml \
					llvmAstPrinter.ml \
					llvmParser.ml \
					llvmLexer.ml \
					llvmAstTranslator.ml \
					ropCodeWriter.ml
objects			:= $(subst .ml,.cmo,$(sources))

packs 			:= extlib,bigarray,str,ocamlgraph
ocaml_opts		:= -package $(packs) -linkpkg -thread

all: ropc

ropc: $(objects)
	ocamlfind ocamlc $(ocaml_opts) $(inc_params) $(libs) $(deps) $(objects) ropc.ml -o $@
	mv $@ $(bin_dir)/$@-bap-0.4

ropCodeWriter.cmo: ropCodeWriter.ml
	ocamlfind ocamlc -c -package extlib -I $(common_dir) ropCodeWriter.ml

regSets.cmo: regSets.ml roplAst.cmo ssaForm.cmo
	ocamlc -c -I $(common_dir) regSets.ml

analysis.cmo: analysis.ml roplAst.cmo ssaFormPrinter.cmo
	ocamlc -c -I $(common_dir) analysis.ml

ssaForm.cmo: ssaForm.ml
	ocamlc -c -I $(common_dir) ssaForm.ml

ssaFormPrinter.cmo: ssaFormPrinter.ml
	ocamlc -c -I $(common_dir) ssaFormPrinter.ml

roplAst.cmo: roplAst.ml
	ocamlc -c -I $(common_dir) roplAst.ml

roplAstRewriter.cmo: roplAstRewriter.ml ssaForm.cmo
	ocamlc -c -I $(common_dir) roplAstRewriter.ml

llvmAst.cmo: llvmAst.ml
	ocamlc -c llvmAst.ml

llvmAstPrinter.cmo: llvmAstPrinter.ml
	ocamlc -c llvmAstPrinter.ml

llvmAstTranslator.cmo: llvmAstTranslator.ml
	ocamlc -c llvmAstTranslator.ml

roplLexer.cmo: roplLexer.mll roplParser.cmo
	ocamllex roplLexer.mll

	ocamlc -c -I $(common_dir) roplLexer.ml

roplParser.cmo: roplParser.mly roplAst.cmo
	ocamlyacc roplParser.mly

	ocamlc -c -I $(common_dir) roplParser.mli
	ocamlc -c -I $(common_dir) roplParser.ml

llvmLexer.cmo: llvmParser.cmo llvmLexer.mll
	ocamllex llvmLexer.mll

	ocamlc -c llvmLexer.ml

llvmParser.cmo: llvmAst.cmo llvmParser.mly
	ocamlyacc llvmParser.mly

	ocamlc -c llvmParser.mli
	ocamlc -c llvmParser.ml

clean:
	rm -f *.o *.cmo *.cmi *.cmx

	rm -f roplLexer.ml
	rm -f roplParser.mli roplParser.ml

	rm -f llvmLexer.ml
	rm -f llvmParser.mli llvmParser.ml

	rm -f $(bin_dir)/ropc-bap-0.4
