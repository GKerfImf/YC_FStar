module Source
	type position = 
		| Position : absoluteOffset:int -> line:int -> column:int -> position 
	type t =
		| T : text:string -> startPos:position -> endPos:position -> file:string -> t

(*	type cand (p1:Type) (p2:Type) : Type =
  		| Conj : h1:p1 -> h2:p2 -> cand p1 p2

	https://github.com/FStarLang/FStar/
		blob/b076cca702e7b7da2d18d9a46388c9157ca92575/lib/FStar.Constructive.fst *)

(*	type position (p1:Type) (p2:Type) (p3:Type) : Type =
  		| Position : absoluteOffset:p1 -> line:p2 -> column:p3 -> position p1 p2 p3
  	vs
	type position = 
		|Position : absoluteOffset:int -> line:int -> column:int -> position 
*)