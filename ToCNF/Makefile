#VERFILES=\
	IL.fst\
    Yard.Core.Conversions.Helpers.fst\
    Yard.Core.Conversions.SplitLongRule.fst\
    Yard.Core.Conversions.DeleteEpsRule.fst\
    Yard.Core.Conversions.DeleteChainRule.fst\
    Yard.Core.Conversions.DeleteUseless.fst\
    Yard.Core.Conversions.RenameTerm.fst\
    Yard.Core.Conversions.ToCNF.fst\
    Main.fst

VERFILES=\
	IL.fst\
    Yard.Core.Conversions.Helpers.fst\
    Yard.Core.Conversions.SplitLongRule.fst
    
LIB_FILES =\
	FStar.Set.fsi\
	FStar.Heap.fst\
	FStar.ST.fst\
	FStar.All.fst\
	FStar.IO.fsti \
	FStar.List.fst\
	FStar.List.Tot.fst\
	FStar.ListProperties.fst\
	FStar.String.fst

FSTAR_HOME = 'C:/Program Files/FStar/fstar_0.9.2.0_Windows_x64/fstar'
FS_LIBS = $(FSTAR_HOME)/bin/FSharp.PowerPack.dll
LIB = $(FSTAR_HOME)/lib
BIN = $(FSTAR_HOME)/bin
FSTAR = $(BIN)/fstar.exe


ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility -r $(FSTAR_HOME)/bin/FSharp.PowerPack.dll
else
FSC     = fsharpc --mlcompatibility -r $(FSTAR_HOME)/bin/FSharp.PowerPack.dll
endif


add_stdlib_prefix = $(addprefix $(FSTAR_HOME)/lib/,$(1))
STDLIB = $(call add_stdlib_prefix, $(LIB_FILES))


all: ver extrToCNFOCaml

ver: $(VERFILES)
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.IO $(STDLIB) $^

extrToCNFOCaml: $(VERFILES)
	$(FSTAR) --use_native_int --odir out --codegen OCaml --admit_fsi FStar.Set --admit_fsi FStar.IO FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti FStar.List.fst FStar.List.Tot.fst FStar.ListProperties.fst $^
	cp $(LIB)/ml/native_int/prims.ml $(LIB)/ml/FStar_IO.ml $(LIB)/ml/FStar_All.ml out
	(cd out; ocamlc -o ToCNF.exe nums.cma prims.ml FStar_IO.ml FStar_All.ml FStar_List.ml FStar_List_Tot.ml FStar_ListProperties.ml IL.ml Yard_Core_Conversions_Helpers.ml Yard_Core_Conversions_DeleteChainRule.ml Main.ml)
	./out/ToCNF.exe

# Fail
#ToCNFFSharp: Il.fst Helpers.fst DeleteChainRule.fst Main.fst
#	$(FSTAR) --use_native_int --odir out --codegen FSharp --admit_fsi FStar.Set --admit_fsi FStar.IO FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti --no_extract FStar.List.fst FStar.List.Tot.fst $^
#	cp $(LIB)/fs/native_int/prims.fs $(LIB)/fs/io.fs $(LIB)/fs/all.fs out
#	(cd out; $(FSC) -o ToCNF.exe prims.fs io.fs all.fs FStar.List.fs FStar.List.Tot.fs Il.fs Helpers.fs DeleteChainRule.fs Main.fs)
#	./out/ToCNF.exe
