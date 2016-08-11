module TestEquLikeInCoqPaper
open FStar.Constructive


type sf (non_terminal: eqtype) (terminal: eqtype) = list (cor non_terminal terminal)
type sentence (terminal: eqtype) = list terminal

let terminal_lift (#nt: eqtype) (#t: eqtype) (term: t): (cor nt t) = IntroR term


noeq type cfg (nt: eqtype) (t: eqtype) = {
  start_symbol: nt;
  rules: nt -> list (cor nt t) -> Type
}


noeq type derives (#nt: eqtype) (#t: eqtype) (g: cfg nt t) (old_sf: sf nt t) (new_sf: sf nt t) =
	| DerivesRefl: sf1: sf nt t -> derives g old_sf new_sf
    | DerivesStep:
        sf1: sf nt t
        -> sf2: sf nt t
        
        -> left: nt 
        -> right: (sf nt t) {g.rules left right /\ sf1 @ right @ sf2 = new_sf} 
        
        -> derives g old_sf (sf1 @  IntroL left :: sf2) 
        
        -> derives g old_sf new_sf 


type generates (#nt: eqtype) (#t: eqtype) (g: cfg nt t) (s: sf nt t) =
    derives g [IntroL g.start_symbol] s

type produces (#nt: eqtype) (#t: eqtype) (g: cfg nt t) (s: sentence t) =
    generates g (List.Tot.map terminal_lift s)

type g_equiv (#nt1: eqtype) (#nt2: eqtype) (#t: eqtype) (g1: cfg nt1 t) (g2: cfg nt2 t): Type =
  forall (s: sentence t). produces g1 s <==> produces g2 s




type nt1 = | S1 | A1 | B1
type nt2 = | S2 | A2 | B2
type t = | X | Y | Z

let rules1 (l: nt1) (r: list (cor nt1 t)): Type = 
    match l, r with
    | S1, [IntroL A1] -> True
    | A1, [IntroR X] -> True
    | _,_ -> False
    
let rules2 (l: nt2) (r: list (cor nt2 t)): Type = 
    match l, r with
    | S2, [IntroR X] -> True
    | _,_ -> False   
    
    


let g1: cfg nt1 t = {start_symbol = S1; rules = rules1} 

let g2: cfg nt2 t = {start_symbol = S2; rules = rules2}

  
let kek = 
	assert ( derives g1 [IntroL A1] [IntroL A1] ) ; 	// Fail 
    //assert (g_equiv g1 g2);
    0