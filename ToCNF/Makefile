#VERFILES=\
#	IL.fst\
#    Yard.Core.Conversions.Helpers.fst\
#    Yard.Core.Conversions.SplitLongRule.fst\
#    Yard.Core.Conversions.DeleteEpsRule.fst\
#    Yard.Core.Conversions.DeleteChainRule.fst\
#    Yard.Core.Conversions.DeleteUseless.fst\
#    Yard.Core.Conversions.RenameTerm.fst\
#    Yard.Core.Conversions.ToCNF.fst\
#    Main.fst

VERFILES=\
	IL.fst\
    Yard.Core.Conversions.Helpers.fst\
    Yard.Core.Conversions.DeleteChainRule.fst\
    Equ.fst\
    Main.fst
    
 
LIB_FILES = FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.PredicateExtensionality.fst\
    FStar.TSet.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Float.fsti FStar.IO.fsti\
    FStar.List.Tot.fst FStar.ListProperties.fst
	


FSTAR_HOME = ~/FStar
LIB = $(FSTAR_HOME)/lib
BIN = $(FSTAR_HOME)/bin
FSTAR = $(BIN)/fstar.exe



#all: ver
all: extrToCNFOCaml 


ver: $(VERFILES)
	$(FSTAR) --explicit_deps $(LIB_FILES) $^

extrToCNFOCaml: $(VERFILES)
	$(FSTAR)  --z3timeout 10000 --explicit_deps --use_native_int --odir out --codegen OCaml $(LIB_FILES) $^
	cp $(LIB)/ml/MkPrims.ml $(LIB)/ml/native_int/prims.ml $(LIB)/ml/FStar_IO.ml $(LIB)/ml/FStar_All.ml out
	(cd out; ocamlc -o ToCNF.exe nums.cma MkPrims.ml prims.ml FStar_IO.ml FStar_All.ml FStar_List_Tot.ml IL.ml Yard_Core_Conversions_Helpers.ml Yard_Core_Conversions_DeleteChainRule.ml Equ.ml Main.ml)
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