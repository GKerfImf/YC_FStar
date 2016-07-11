VERFILES=\
    IL.fst\
    Yard.Core.Conversions.TransformAux.fst\
    Yard.Core.Conversions.DeleteChainRule.fst\
    Yard.Core.Conversions.RenameTerm.fst

LIB_FILES =\
	FStar.Set.fsi\
	FStar.Heap.fst\
	FStar.ST.fst\
	FStar.All.fst\
	FStar.List.fst\
	FStar.List.Tot.fst\
	FStar.ListProperties.fst\
	FStar.String.fst

FSTAR_HOME = 'C:/Program Files/FStar/fstar_0.9.2.0_Windows_x64/fstar'
add_stdlib_prefix = $(addprefix $(FSTAR_HOME)/lib/,$(1))
STDLIB = $(call add_stdlib_prefix, $(LIB_FILES))

all: $(VERFILES)
	fstar --admit_fsi FStar.Set $(STDLIB) $^