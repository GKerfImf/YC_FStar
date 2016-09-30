#VERFILES=\
	IL.fst\
    Yard.Core.Conversions.Helpers.fst\
    Yard.Core.Conversions.DeleteStartSymbol.fst\
    Yard.Core.Conversions.SplitLongRule.fst\
    Yard.Core.Conversions.DeleteEpsRule.fst\
    Yard.Core.Conversions.DeleteChainRule.fst\
    Yard.Core.Conversions.DeleteUseless.fst\
    Yard.Core.Conversions.RenameTerm.fst\
    Yard.Core.Conversions.ToCNF.fst\
    Printer.fst\
    Equ.fst\
    Main.fst


VERFILES=\
	IL.fst\
    Yard.Core.Conversions.Helpers.fst\
    Yard.Core.Conversions.DeleteStartSymbol.fst\
    Printer.fst\
    Main.fst
 
LIB_FILES = FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.PropositionalExtensionality.fst FStar.PredicateExtensionality.fst\
    FStar.TSet.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Float.fsti FStar.IO.fsti\
    FStar.List.Tot.fst FStar.ListProperties.fst FStar.Constructive.fst
	


FSTAR_HOME = ~/FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
LIB = $(FSTAR_HOME)/lib
BIN = $(FSTAR_HOME)/bin
FSTAR = $(BIN)/fstar.exe



#all: ver2
all: extrToCNFOCaml 


ver: $(VERFILES)
	$(FSTAR) --z3timeout 100 --explicit_deps $(LIB_FILES) $^


ver1: $(VERFILES)
	$(FSTAR) --explicit_deps $(LIB_FILES) $^

ver2: $(VERFILES)
	$(FSTAR) --print_fuels --z3timeout 10 --initial_fuel 8 --initial_ifuel 8 --max_fuel 64 --max_ifuel 16 --explicit_deps $(LIB_FILES) $^


extrToCNFOCaml: $(VERFILES)
	$(MAKE) -C $(ULIB_ML)
	#$(FSTAR) --explicit_deps --odir out --codegen OCaml $(LIB_FILES) $^
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml $^
	#cp $(LIB)/ml/MkPrims.ml $(LIB)/ml/prims.ml $(LIB)/ml/FStar_IO.ml $(LIB)/ml/FStar_All.ml out
	#(cd out; ocamlc -o ToCNF.exe nums.cma MkPrims.ml prims.ml FStar_IO.ml FStar_All.ml FStar_List_Tot.ml IL.ml Yard_Core_Conversions_Helpers.ml Yard_Core_Conversions_DeleteEpsRule.ml Printer.ml Main.ml)
	#(cd out; ocamlc -o ToCNF.exe nums.cma MkPrims.ml Big_int_Z.ml prims.ml IL.ml Yard_Core_Conversions_Helpers.ml)
	(cd out; $(OCAMLOPT) FStar_List_Tot.ml IL.ml Yard_Core_Conversions_Helpers.ml Printer.ml Yard_Core_Conversions_DeleteStartSymbol.ml Main.ml -o ToCNF.exe)
	./out/ToCNF.exe



FS_LIBS = $(FSTAR_HOME)/bin/FSharp.PowerPack.dll

ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility -r $(FSTAR_HOME)/bin/FSharp.PowerPack.dll
else
FSC     = fsharpc --mlcompatibility -r $(FSTAR_HOME)/bin/FSharp.PowerPack.dll
endif

# Fail
#extrToCNFFSharp: $(VERFILES)
#	$(FSTAR) --odir out --codegen FSharp $(LIB_FILES) $^
#	cp $(LIB)/fs/prims.fs $(LIB)/fs/io.fs $(LIB)/fs/all.fs out
#	(cd out; $(FSC) -o ToCNF.exe prims.fs io.fs all.fs FStar.List.Tot.fs IL.fs Yard.Core.Conversions.Helpers.fs Yard.Core.Conversions.DeleteChainRule.fs Main.fs)
#	./out/ToCNF.exe


#add_stdlib_prefix = $(addprefix $(FSTAR_HOME)/ulib/,$(1))
#STDLIB = $(call add_stdlib_prefix, $(LIB_FILES))
#STDLIB = $(LIB_FILES)
