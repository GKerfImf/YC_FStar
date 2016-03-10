VERFILES=IL.fst Yard.Core.Namer.fst Yard.Core.Conversions.TransformAux.fst Yard.Core.Conversions.ToCNF.fst Main.fst
include ../Makefile.include

LIB=../../lib
BIN=../../bin
FS_LIBS=$(BIN)/FSharp.PowerPack.dll

ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility $(addprefix -r , $(FS_LIBS))
else
FSC     = fsharpc --mlcompatibility $(addprefix -r , $(FS_LIBS))
endif

all: all-pos fs

all-pos: basictests

basictests: $(VERFILES)
	$(FSTAR_OR_NUBUILD) --admit_fsi FStar.Set $(STDLIB) $(call add_stdlib_prefix, FStar.Int32.fst) $^

fs: out Main.fst
	$(FSTAR) --odir out --admit_fsi FStar.Set $(STDLIB) --codegen FSharp IL.fst Yard.Core.Namer.fst Yard.Core.Conversions.TransformAux.fst Yard.Core.Conversions.ToCNF.fst Main.fst
	cp $(FS_LIBS) out
	$(FSC) -o out/Main.exe $(LIB)/fs/prims.fs $(LIB)/fs/io.fs out/Main.fs
	$(FSRUNTIME) ./out/Main.exe
	

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
