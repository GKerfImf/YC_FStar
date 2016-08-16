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


let terminal_lift (t: term): symbol = IntroR t

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
                            True
                            /\ sf1 @ right @ sf2 = new_sf 
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

let g1_copy: cfg = {
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

(*
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
*)

(*
// F* only unfolds id_trans
val id_transform: cfg -> Tot cfg
let id_transform g = g 

let test_14 = assert (forall (x: sf). derives g1 sf_0 x ==> derives (id_transform g1) sf_0 x)
let test_15 = assert (forall (x: sf) (g: cfg). derives g sf_0 x ==> derives (id_transform g) sf_0 x)
*)

(*
// if g1 = g2 then F* don't use "Derives"

val rev_transform: g1:cfg -> Tot (g2: cfg { g1 = g2 } ) 
let rev_transform g = 
    assume (false);
    {g with rules = List.Tot.rev g.rules} 

let test_16 = assert (forall (x: sf). derives g1 sf_0 x ==> derives (rev_transform g1) sf_0 x)

let test_17 = assert (forall (x: sf) (g: cfg). derives g sf_0 x ==> derives (rev_transform g) sf_0 x) // Fail
*)



assume val generates: g:cfg -> new_sf:sf -> Type 

assume Generates: 
    forall (g: cfg) (new_sf: sf). 
        generates g new_sf <==> derives g [IntroL g.start_symbol] new_sf

(*
let test_18 = assert (generates g1 sf_0) //Ok

let test_19 = assert (generates g1 sf_1) //Ok
let test_20 = assert (generates g1 sf_2) //Ok
let test_21 = assert (generates g1 sf_3) //Ok

let test_22 = assert (generates g1 sf_4) //Ok
let test_23 = assert (generates g1 sf_5) //Ok
let test_24 = assert (generates g1 sf_6) //Ok
let test_25 = assert (generates g1 sf_7) //Ok
let test_26 = assert (generates g1 sf_8) //Ok
let test_27 = assert (generates g1 sf_9) //Ok

let test_28 = assert (generates g1 sf_10) //Ok
let test_29 = assert (generates g1 sf_11) //Ok
let test_30 = assert (generates g1 sf_12) //Ok

let test_31 = assert (generates g1 sf_13) //Ok
*)


assume val produces: g:cfg -> sent: sentence -> Type 

assume Produces: 
    forall (g: cfg) (sent: sentence). 
        produces g sent <==> generates g (List.Tot.map terminal_lift sent) 
(*
let test_32 = assert (produces g1 [T "O"]) //Ok
let test_33 = assert (produces g1 [T "("; T "O"; T ")"]) //Ok
let test_34 = assert (produces g1 [T "("; T "("; T "O"; T ")"; T ")"]) //Ok
let test_35 = assert (produces g1 [T "("; T "("; T "O"; T ")"; T ")"; T "("; T "O"; T ")"]) //Ok
*)



assume val op_Bar_Equals_Bar: g1:cfg -> g1:cfg -> Type 

assume GrEqu: 
    forall (g1: cfg) (g2: cfg). 
        g1 |=| g2 <==> (forall sent. produces g1 sent <==> produces g2 sent)

let test_36 = assert ( g1 |=| g1_copy )


(*
val permut_tr_eq_Lemma: g:cnf ->
    Lemma 
        (requires (g.start_symbol = g.start_symbol /\ (forall r. List.Tot.mem r g1.rules <==> List.Tot.mem r g2.rules))) 
        (ensures (List.Tot.length (powerset l) <= pow2 (List.Tot.length l)))
        [SMTPat (powerset l)]
let rec rev_tr_eq_Lemma #a l = 
    match l with
    | [] -> ()
    | hd::tl -> admit ()
*)

val rev_transform: g1:cfg -> Tot (g2: cfg {g1.start_symbol = g2.start_symbol /\ (forall r. List.Tot.mem r g1.rules <==> List.Tot.mem r g2.rules) } ) 
let rev_transform g = 
    assume (false);
    {g with rules = List.Tot.rev g.rules} 

val rev_tr_eq_Lemma: g1:cfg ->
    Lemma 
        (requires True) 
        (ensures (
            let g2 = rev_transform g1 in
            forall n_sf. derives g1 [IntroL g1.start_symbol] n_sf <==> derives g2 [IntroL g2.start_symbol] n_sf
            )
        )
let rec rev_tr_eq_Lemma g1 = 




    let g2 = rev_transform g1 in


    assert ( g1.start_symbol = g2.start_symbol );
    assert ( forall r. List.Tot.mem r g1.rules <==> List.Tot.mem r g2.rules );

    let old_sf = [IntroL g1.start_symbol] in



    assert (derives g1 old_sf old_sf ==> derives g2 old_sf old_sf) ;


    // Temp
    assume (

        forall left right sf1 sf2 l_sf r_sf. 

            List.Tot.mem (left, right) g1.rules 
            /\ (sf1 @ [IntroL left] @ sf2) = l_sf 
            /\ (sf1 @ right @ sf2) = r_sf 
            /\ (derives g1 old_sf l_sf ==> derives g2 old_sf l_sf) ==> 


            //derives g1 old_sf r_sf ==> derives g2 old_sf r_sf


            (
                         (exists (leftn: nonterm) (rightn: sf).
                            True
                            /\ List.Tot.mem (leftn, rightn) g1.rules
                            ///\ leftn = left 
                            //\ rightn = right
                                /\ (let (sf1,sf2) = splitR [] r_sf in
                                    sf1 @ rightn @ sf2 = r_sf /\ derives g1 old_sf (sf1 @ [IntroL leftn] @ sf2))))
            ==> 

            (
                (exists (leftn: nonterm) (rightn: sf).
                    True
                    /\ leftn = left 
                    /\ rightn = right
                        /\ (let (sf1n,sf2n) = splitR [] r_sf in
                            sf1 = sf1n 
                            /\ sf2 = sf2n
                            /\ sf1n @ right @ sf2n = r_sf
                            /\ sf1n @ [IntroL left] @ sf2n = l_sf
                            /\ derives g2 old_sf (sf1n @ [IntroL left] @ sf2n)

                            )
                )
             )

        ) ;

    // Temp
    assert (

        forall left right sf1 sf2 l_sf r_sf. 

            List.Tot.mem (left, right) g1.rules 
            /\ (sf1 @ [IntroL left] @ sf2) = l_sf 
            /\ (sf1 @ right @ sf2) = r_sf 
            /\ (derives g1 old_sf l_sf ==> derives g2 old_sf l_sf) ==> 


            //derives g1 old_sf r_sf ==> derives g2 old_sf r_sf


            (
                         (exists (leftn: nonterm) (rightn: sf).
                            True
                            /\ List.Tot.mem (leftn, rightn) g1.rules
                            //\ leftn = left 
                            //\ rightn = right
                                /\ (let (sf1,sf2) = splitR [] r_sf in
                                    sf1 @ rightn @ sf2 = r_sf /\ derives g1 old_sf (sf1 @ [IntroL leftn] @ sf2))))
            ==> 

            (
                         (exists (leftn: nonterm) (rightn: sf).
                            True
                            /\ List.Tot.mem (leftn, rightn) g2.rules
                            //\ leftn = left 
                            //\ rightn = right
                                /\ (let (sf1,sf2) = splitR [] r_sf in
                                    sf1 @ rightn @ sf2 = r_sf /\ derives g2 old_sf (sf1 @ [IntroL leftn] @ sf2))))

        ) ;

    // Temp
    assert (

        forall left right sf1 sf2 l_sf r_sf. 

            List.Tot.mem (left, right) g1.rules 
            /\ (sf1 @ [IntroL left] @ sf2) = l_sf 
            /\ (sf1 @ right @ sf2) = r_sf 
            /\ (derives g1 old_sf l_sf ==> derives g2 old_sf l_sf)

                ==> derives g1 old_sf r_sf ==> derives g2 old_sf r_sf
        ) ;


// Induction axiom
    assume (
        forall (g1: cfg) (g2: cfg) (old_sf: sf).
            (derives g1 old_sf old_sf ==> derives g2 old_sf old_sf) /\ 

            (forall left right sf1 sf2. 
                List.Tot.mem (left, right) g1.rules /\ (derives g1 old_sf (sf1 @ [IntroL left] @ sf2) ==> derives g2 old_sf (sf1 @ [IntroL left] @ sf2))
                    ==> (derives g1 old_sf (sf1 @ right @ sf2) ==> derives g2 old_sf (sf1 @ right @ sf2))
            ) 

            ==> (forall (new_sf: sf). derives g1 old_sf new_sf ==> derives g2 old_sf new_sf)
    
    );

    assert ( forall new_sf. derives g1 old_sf new_sf ==> derives g2 old_sf new_sf );
    assume ( forall new_sf. derives g1 old_sf new_sf <==> derives g2 old_sf new_sf );
    ()

let test_37 g1 = 
    let g2 = rev_transform g1 in

    assert ( g1.start_symbol = g2.start_symbol ); 
    assert (forall r. List.Tot.mem r g1.rules <==> List.Tot.mem r g2.rules);

    rev_tr_eq_Lemma g1 ;

    assert ( forall n_sf. derives g1 [IntroL g1.start_symbol] n_sf <==> derives g2 [IntroL g2.start_symbol] n_sf);
    assert ( forall n_sf. generates g1 n_sf <==> generates g2 n_sf );
    assert ( forall sent. produces g1 sent <==> produces g2 sent );
    assert ( g1 |=| g2 )