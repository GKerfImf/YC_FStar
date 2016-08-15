module EquANewHope 
open FStar.Constructive 
open FStar.List.Tot

type nonterm = 
    | NT of string 

type term = 
    | T of string 

type symbol = cor nonterm term 
type sf = list symbol 
type sentence = list term 

type cfg = { 
    start_symbol: nonterm; 
    rules: list (nonterm * sf) 
} 


assume val derives: g:cfg -> old_sf:sf -> new_sf:sf -> Type 

(*
//Fail

val s_nhd_ntl: nat -> list 'a -> list 'a -> Tot ((list 'a) * (list 'a))
let rec s_nhd_ntl n nhd ntl =
	assume (false);
    if n = 0 then (nhd, ntl) else s_nhd_ntl (n-1) (nhd @ [hd ntl]) (tl ntl)

val helper: #a:eqtype -> list a -> list a -> list a -> Tot ((list a) * (list a))
let rec helper #a sub_lst acc1 acc2 = 

    if (length acc2 > length sub_lst) 
    then
    	begin
	    	let (l,r) = s_nhd_ntl (length sub_lst) [] acc2 in 
	    	assume(false);
            if l = sub_lst then (acc1, r) else helper sub_lst (acc1 @ [hd acc2]) (tl acc2)
    	end
    else ([],[])


let splitR sub_lst lst = helper #symbol sub_lst [] lst
*)


(*
// something like oracle:

let splitR sub_lst lst =
	match sub_lst, lst with
	| [IntroR (T "("); IntroL (NT "S"); IntroR (T ")")], 	[IntroR (T "("); IntroR (T "("); IntroL (NT "S"); IntroR (T ")"); IntroR (T ")")] 	-> [IntroR (T "(")], [IntroR (T ")")]
	| [IntroL (NT "S"); IntroL (NT "S")], 					[IntroR (T "("); IntroL (NT "S"); IntroL (NT "S"); IntroR (T ")")] 					-> [IntroR (T "(")], [IntroR (T ")")] 
	| [], 													[IntroR (T "("); IntroR (T ")")] 													-> [IntroR (T "(")], [IntroR (T ")")] 
	| [IntroR (T "("); IntroL (NT "S"); IntroR (T ")")], 	[IntroR (T "("); IntroL (NT "S"); IntroR (T ")"); IntroL (NT "S")] 					-> [], [IntroL (NT "S")]
	| [IntroL (NT "S"); IntroL (NT "S")], 					[IntroL (NT "S"); IntroL (NT "S"); IntroL (NT "S")] 								-> [], [IntroL (NT "S")]
	| [IntroR (T "("); IntroL (NT "S"); IntroR (T ")")], 	[IntroL (NT "S"); IntroR (T "("); IntroL (NT "S"); IntroR (T ")")] 					-> [IntroL (NT "S")], []
	| _,_ -> [],[]
*)

// something like oracle, extended 
val splitR: sf -> sf -> Tot (sf * sf)
let rec splitR acc1 acc2 = 
	match acc2 with
	| IntroR (T "(") :: IntroL (NT "S") :: IntroR (T ")") ::tl -> acc1, tl
	| IntroL (NT "S") :: IntroL (NT "S") :: tl -> acc1, tl
	| IntroR (T "O")::tl -> acc1, tl

    | hd::tl -> assume (false); splitR (acc1 @ [hd]) tl
    | _ -> [],[]



assume Derives: 
    forall (g: cfg) (old_sf: sf) (new_sf: sf). 
        derives g old_sf new_sf <==> 
            old_sf = new_sf 
            \/ (exists (left: nonterm) (right: sf).
                    List.Tot.mem (left, right) g.rules 
                    /\ (let (sf1,sf2) = splitR [] new_sf in //let (sf1,sf2) = splitR right new_sf in 
                            sf1 @ right @ sf2 = new_sf 
                            /\ derives g old_sf (sf1 @ [IntroL left] @ sf2)
                        )
                ) 
            
let g1: cfg = {
    start_symbol = NT "S"; 
    rules = [
        (NT "S", [IntroR (T "("); IntroL (NT "S"); IntroR (T ")")]);
        (NT "S", [IntroL (NT "S"); IntroL (NT "S")]);
        (NT "S", [IntroR (T "O")])
    ]
} 

let sf_0: sf = [IntroL (NT "S")] 

let sf_1: sf = [IntroR (T "("); IntroL (NT "S"); IntroR (T ")")] 
let sf_2: sf = [IntroL (NT "S"); IntroL (NT "S")]
let sf_3: sf = [IntroR (T "O")] 

let sf_4: sf = [IntroR (T "("); IntroR (T "("); IntroL (NT "S"); IntroR (T ")"); IntroR (T ")")] 
let sf_5: sf = [IntroR (T "("); IntroL (NT "S"); IntroL (NT "S"); IntroR (T ")")] 
let sf_6: sf = [IntroR (T "("); IntroR (T "O"); IntroR (T ")")]
let sf_7: sf = [IntroR (T "("); IntroL (NT "S"); IntroR (T ")"); IntroL (NT "S")]
let sf_8: sf = [IntroL (NT "S"); IntroL (NT "S"); IntroL (NT "S")]
let sf_9: sf = [IntroL (NT "S"); IntroR (T "("); IntroL (NT "S"); IntroR (T ")")]

let sf_10: sf = [IntroR (T "("); IntroR (T "("); IntroR (T "("); IntroL (NT "S"); IntroR (T ")"); IntroR (T ")"); IntroR (T ")")] 
let sf_11: sf = [IntroR (T "("); IntroR (T "("); IntroL (NT "S"); IntroL (NT "S"); IntroR (T ")"); IntroR (T ")")] 
let sf_12: sf = [IntroR (T "("); IntroR (T "("); IntroR (T "O"); IntroR (T ")"); IntroR (T ")")] 

let sf_13: sf = [IntroR (T "("); IntroR (T "("); IntroR (T "O"); IntroR (T ")"); IntroR (T ")"); IntroR (T "("); IntroR (T "O"); IntroR (T ")")]


let test_0 = assert (derives g1 sf_0 sf_0) //Ok

let test_1 = assert (derives g1 sf_0 sf_1) //Ok
let test_2 = assert (derives g1 sf_0 sf_2) //Ok
let test_3 = assert (derives g1 sf_0 sf_3) //Ok

let test_4 = assert (derives g1 sf_0 sf_4) //Ok
let test_5 = assert (derives g1 sf_0 sf_5) //Ok
let test_6 = assert (derives g1 sf_0 sf_6) //Ok
let test_7 = assert (derives g1 sf_0 sf_7) //Ok
let test_8 = assert (derives g1 sf_0 sf_8) //Ok
let test_9 = assert (derives g1 sf_0 sf_9) //Ok

let test_10 = assert (derives g1 sf_0 sf_10) //Ok
let test_11 = assert (derives g1 sf_0 sf_11) //Ok
let test_12 = assert (derives g1 sf_0 sf_12) //Ok

let test_13 = assert (derives g1 sf_0 sf_13) //Ok


// ¯\_(ツ)_/¯
val id_transform: cfg -> Tot cfg
let id_transform g = g 

let test_14 = assert (forall (x: sf). derives g1 sf_0 x ==> derives (id_transform g1) sf_0 x) // Ok
let test_15 = assert (forall (x: sf) (g: cfg). derives g sf_0 x ==> derives (id_transform g) sf_0 x) // Lol, this is works too 


val rev_transform: g1:cfg -> Tot (g2: cfg {forall r. List.Tot.mem r g1.rules <==> List.Tot.mem r g2.rules} )
let rev_transform g = 
    assume (false);
    {g with rules = List.Tot.rev g.rules} 

let test_16 = assert (forall (x: sf). derives g1 sf_0 x ==> derives (rev_transform g1) sf_0 x) // Fail
let test_17 = assert (forall (x: sf) (g: cfg). derives g sf_0 x ==> derives (rev_transform g) sf_0 x) // Fail



(* 
type generates (#nt: eqtype) (#t: eqtype) (g: cfg nt t) (s: sf nt t) = 
derives g [IntroL g.start_symbol] s 

type produces (#nt: eqtype) (#t: eqtype) (g: cfg nt t) (s: sentence t) = 
generates g (List.Tot.map terminal_lift s) 

type g_equiv (#nt1: eqtype) (#nt2: eqtype) (#t: eqtype) (g1: cfg nt1 t) (g2: cfg nt2 t): Type = 
forall (s: sentence t). produces g1 s <==> produces g2 s 

*)