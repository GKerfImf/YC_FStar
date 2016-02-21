include ../Makefile.include

fs:
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
	$(FSTAR) Source.fst Production.fst Rule.fst Grammar.fst Definition.fst Yard.Core.Conversions.ExpandInnerAlt.fst Main.fst
