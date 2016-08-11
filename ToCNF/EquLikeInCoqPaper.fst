module EquLikeInCoqPaper
open FStar.Constructive

//assume new type nt: eqtype
//assume new type t: eqtype

type sf (non_terminal: eqtype) (terminal: eqtype) = list (cor non_terminal terminal)
type sentence (terminal: eqtype) = list terminal

//Notation nlist:= (list non_terminal).
//Notation tlist:= (list terminal).
//Notation symbol:= (non_terminal + terminal)%type.

noeq type cfg (nt: eqtype) (t: eqtype) = {
  start_symbol: nt;
  rules: nt -> list (cor nt t) -> Type  //Type
}


noeq type derives (nt: eqtype) (t: eqtype) (g: cfg nt t) (old_sf: sf nt t) (new_sf: sf nt t) =
	| DerivesRefl: sf1: sf nt t -> derives nt t g old_sf new_sf
    | DerivesStep:
        sf1: sf nt t
        -> sf2: sf nt t
        
        -> left: nt 
        -> right: (sf nt t) {g.rules left right /\ sf1 @ right @ sf2 = new_sf} 
        
        -> derives nt t g old_sf (sf1 @  IntroL left :: sf2) 
        
        -> derives nt t g old_sf new_sf 



noeq type generates (nt: eqtype) (t: eqtype) (g: cfg nt t) (s: sf nt t) =
    derives nt t g [IntroL g.start_symbol] s


let terminal_lift (nt: eqtype) (t: eqtype) (term: t): cor nt t = IntroR term

noeq type produces (nt: eqtype) (t: eqtype) (g: cfg nt t) (s: sentence t) =
    generates nt t g (List.Tot.map (terminal_lift nt t) s)


(*
let appears (nt: eqtype) (t: eqtype) (g: cfg nt t) (s: cor nt t) =
  match s with
  | IntroL n -> exists (left: non_terminal) (right: sf),
             rules g left right /\ ((n=left) \/ (In (inl n) right))
  | IntroR t -> exists (left: non_terminal) (right: sf),
             rules g left right /\ In (inr t) right
*)

let appears (nt: eqtype) (t: eqtype) (g: cfg nt t) (s: cor nt t): Type = False


let g_equiv (nt1: eqtype) (nt2: eqtype) (t: eqtype) (g1: cfg nt1 t) (g2: cfg nt2 t): Type =
  forall (s: sentence t). produces nt1 t g1 s <==> produces nt2 t g2 s
  
let useful (nt: eqtype) (t: eqtype) (g: cfg nt t) (s: cor nt t): Type =
    match s with
    | IntroR t -> True
    | IntroL n -> exists (s: sentence t). derives nt t g [IntroL n] (List.Tot.map (terminal_lift nt t) s)

let useful_sf (nt: eqtype) (t: eqtype) (g: cfg nt t) (l: sf nt t): Type =
  forall (s: cor nt t). List.Tot.mem s l -> useful nt t g s


noeq type g_use_rules (nt: eqtype) (t: eqtype) (g: cfg nt t) (left: nt) (right: sf nt t) =
    | Lift_use :
        leftT: nt { leftT = left /\ useful nt t g (IntroL left) } -> 
        rightT: (sf nt t) { rightT = right /\ g.rules left right /\ useful_sf nt t g right} -> 
        g_use_rules nt t g left right

let g_use (nt: eqtype) (t: eqtype) (g: cfg nt t): cfg nt t = {
  start_symbol = g.start_symbol;
  rules = g_use_rules nt t g
}


let has_no_useless_symbols (nt: eqtype) (t: eqtype) (g: cfg nt t): Type =
  forall (n: nt). appears nt t g (IntroL n) -> useful nt t g (IntroL n)
  

let non_empty (nt: eqtype) (t: eqtype) (g: cfg nt t): Type =
  useful nt t g (IntroL g.start_symbol)


assume val g_use_correct: nt: eqtype -> t: eqtype -> g: cfg nt t ->  
    Lemma 
    (requires True)
    (ensures ( non_empty nt t g ->
        g_equiv nt nt t (g_use nt t g) g /\
        has_no_useless_symbols nt t (g_use nt t g) ))