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
LIB = $(FSTAR_HOME)/ulib
BIN = $(FSTAR_HOME)/bin
FSTAR = $(BIN)/fstar.exe



#all: ver2
#all: extrToCNFOCaml 
all: extrToCNFFSharp

ver: $(VERFILES)
	$(FSTAR) --z3timeout 100 --explicit_deps $(LIB_FILES) $^
 

ver1: $(VERFILES)
	$(FSTAR) --explicit_deps $(LIB_FILES) $^

ver2: $(VERFILES)
	$(FSTAR) --print_fuels  --z3timeout 10 --initial_fuel 8 --initial_ifuel 8 --max_fuel 64 --max_ifuel 16 --explicit_deps $(LIB_FILES) $^


extrToCNFOCaml: $(VERFILES)
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml $^
	(cd out; $(OCAMLOPT) FStar_List_Tot.ml IL.ml Yard_Core_Conversions_Helpers.ml Printer.ml Yard_Core_Conversions_DeleteStartSymbol.ml Main.ml -o ToCNF.exe)
	./out/ToCNF.exe


ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility $(addprefix -r , $(FS_LIBS))
else
FSC     = fsharpc --mlcompatibility $(addprefix -r , $(FS_LIBS))
endif

ifeq ($(OS),Windows_NT)
FSRUNTIME =
else
FSRUNTIME = mono
endif

FS_LIBS=$(BIN)/FSharp.PowerPack.dll

extrToCNFFSharp: $(VERFILES)
	#$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen FSharp $^
	#cp $(FS_LIBS) out
	(cd out; $(FSC) --nowarn:0086 --nowarn:0025 $(LIB)/fs/all.fs $(LIB)/fs/prims.fs $(LIB)/fs/io.fs FStar.List.Tot.fs IL.fs Yard.Core.Conversions.Helpers.fs Printer.fs Yard.Core.Conversions.DeleteStartSymbol.fs Main.fs -o ToCNF.exe)
	$(FSRUNTIME) ./out/ToCNF.exe
