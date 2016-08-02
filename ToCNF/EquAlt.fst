module EquAlt
	open FStar.IO
	open IL
	open Yard.Core.Conversions





	type sentence (patt:eqtype) (expr:eqtype) = terms: list (production patt expr){forall prod. List.Tot.mem prod terms ==> Helpers.isPToken prod}
	type sententialForm (patt:Type) (expr:Type) = list (production patt expr)


//TODO: move to Helpers 
    val create: 
         production 'a 'b -> Tot (elem 'a 'b)
    let create arule = {omit=false; binding=None; checker=None; rule = arule}

//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

	assume val start_symbol: #a:eqtype -> #b:eqtype -> list (rule a b) -> Tot (production a b)

    val start_rule_old_cbs: production source source
    let start_rule_old_cbs = PRef (new_Source0 "S", None)

    val terminal_old_cbs: list (production source source)
    let terminal_old_cbs = [PToken (new_Source0 "("); PToken (new_Source0 ")")]

    val non_terminal_old_cbs: list (production source source)
    let non_terminal_old_cbs = [PRef (new_Source0 "S", None)]

    val alphabet_old_cbs: list (production source source)
    let alphabet_old_cbs = terminal_old_cbs @ non_terminal_old_cbs

	val old_cbs: list (rule source source)
	let old_cbs = [Helpers.simpleStartRule "S" (List.Tot.map create [PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")")]);
	    Helpers.simpleNotStartRule "S" (List.Tot.map create [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]);
	    Helpers.simpleNotStartRule "S" (List.Tot.map create [])]



    val start_rule_new_cbs: production source source
    let start_rule_new_cbs = PRef (new_Source0 "S", None)

    val terminal_new_cbs: list (production source source)
    let terminal_new_cbs = [PToken (new_Source0 "("); PToken (new_Source0 ")")]

    val non_terminal_new_cbs: list (production source source)
    let non_terminal_new_cbs = [PRef (new_Source0 "S", None); PRef (new_Source0 "S0", None)]

    val alphabet_new_cbs: list (production source source)
    let alphabet_new_cbs = terminal_new_cbs @ non_terminal_new_cbs

	val new_cbs: list (rule source source) 
	let new_cbs = [Helpers.simpleStartRule "S" (List.Tot.map create [PToken (new_Source0 "("); PRef (new_Source0 "S0", None)]);
	    Helpers.simpleNotStartRule "S0" (List.Tot.map create [PRef (new_Source0 "S", None); PToken (new_Source0 ")")]);
	    Helpers.simpleNotStartRule "S" (List.Tot.map create [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]);
	    Helpers.simpleNotStartRule "S" (List.Tot.map create [])]

//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


	assume val is_rule: #a:eqtype -> #b:eqtype -> g: list (rule a b) -> left: production a b -> rigth: list (production a b) -> Tot bool

	type rules (#a:eqtype) (#b:eqtype) (g: list (rule a b)) = 
		| Rules: left: production a b -> rigth: list (production a b) -> rules g


	type derive (#a:eqtype) (#b:eqtype) (g: list (rule a b)) (old_sf: sententialForm a b) = 
		new_sf: (sententialForm a b) {
			(old_sf = new_sf) \/ 

			(exists sf1 sf2 left rigth. 
				is_rule g left rigth 
				/\ sf1 @ [left] @ sf2 = old_sf 
				/\ sf1 @ rigth @ sf2 = new_sf 
			)
		}


	type derives (#a:eqtype) (#b:eqtype) (g: list (rule a b)) (old_sf: sententialForm a b) (new_sf: sententialForm a b) =
		| DerivesRefl: 
			sf1: sententialForm a b {sf1 = old_sf} 
			-> sf2: sententialForm a b {sf2 = new_sf /\ sf1 = sf2} 
			-> derives g old_sf new_sf
		| DerivesStep: 
			left: production a b 
			-> rigth: list (production a b)
			-> sf1: sententialForm a b
			-> sf2: sententialForm a b {sf1 @ rigth @ sf2 = new_sf }
			-> derives g old_sf (sf1 @ [left] @ sf2)
			-> derives g old_sf new_sf


	val d1: sententialForm source source
	let d1 = [PRef (new_Source0 "S", None)]

	//val d2: lderType source source (Helpers.lift cbs) d1
	val d2: sententialForm source source
	let d2 = [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]


	val d12: derives old_cbs d1 d2
	let d12 = DerivesStep (PRef (new_Source0 "S", None)) ([PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]) [] [] (DerivesRefl d1 d1)


	type generates (#a:eqtype) (#b:eqtype) (g: list (rule a b)) = sf: sententialForm a b {derives g [start_symbol g] sf} 

(*
	type derives (#a:eqtype) (#b:eqtype) (g: list (rule a b)) (old_sf: sententialForm a b) (new_sf: sententialForm a b) = 
		| DerivesRefl: forall (s: sententialForm a b). derives g s
		| DerivesStep: forall s1 s2 s3 left rigth. derives g s1 (s2 @ [left] @ s3) -> rule_type g left rigth -> derives g s1 (s2 @ rigth @ s3)
*)




(*
	val testRule1: rule0: (rule source source) {Helpers.isPSeq rule0.body}
	let testRule1 = Helpers.simpleNotStartRule "S" (List.Tot.map create [PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")")])

	val testRule2: rule0: (rule source source) {Helpers.isPSeq rule0.body}
	let testRule2 = Helpers.simpleNotStartRule "S" (List.Tot.map create [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)])

	val testRule3: rule0: (rule source source) {Helpers.isPSeq rule0.body}
	let testRule3 = Helpers.simpleNotStartRule "S" (List.Tot.map create [])
*)


	val replace: #a:eqtype -> #b:eqtype -> production a b -> list (production a b) -> sententialForm a b -> Tot (sententialForm a b)
	let rec replace #a #b lp rp sf = 
		match sf with
		| [] -> []
		| hd::tl -> 
			if Helpers.isPRef hd 
			then if hd = lp then rp @ tl else sf
			else hd :: replace lp rp tl 

	val getProds: #a:eqtype -> #b:eqtype -> rule a b -> Tot (list (production a b))
	let getProds #a #b rule = 
		match rule.body with
		| PSeq(els,_,_) -> List.Tot.map (fun elem -> elem.rule) els
		| _ -> []


(*
//hz
	val getF: #a:eqtype -> #b:eqtype -> rule a b -> Tot (sententialForm a b -> Tot (sententialForm a b))
	let getF #a #b rule = 
		let (lp: production a b ) = PRef (rule.name, None) in
		let (rp: list (production a b) ) = getProds rule in
		fun sf -> replace lp rp sf


	val rewrite: #a:eqtype -> #b:eqtype -> sententialForm a b -> rule a b -> Tot (sententialForm a b)
	let rewrite #a #b sfl rule  = (getF rule) sfl
*)
			     
	val rewrite: #a:eqtype -> #b:eqtype -> sententialForm a b -> rule a b -> Tot (sententialForm a b)
	let rewrite #a #b sfl rule = 
		let lp: production a b  = PRef (rule.name, None) in
		let rp: list (production a b) = getProds rule in
		replace lp rp sfl


	val lderives: a:eqtype -> b:eqtype -> ruleList: list (rule a b) -> oldSF: sententialForm a b -> newSF: sententialForm a b -> Tot bool
	let lderives a b rl oldSF newSF =
		let temp = List.Tot.map (rewrite oldSF) rl in
		List.Tot.existsb (fun sf -> sf = newSF) temp


	val lderivesSeq: a:eqtype -> b:eqtype -> ruleList: list (rule a b) -> list (sententialForm a b) -> Tot bool
	let rec lderivesSeq a b rl listSF =
		match listSF with 
		| h1::h2::tl -> if lderives a b rl h1 h2 then lderivesSeq a b rl (h2::tl) else false
		| _ -> true


	//type lderType (a: eqtype) (b: eqtype) (ruleList: list (rule a b)) (oldSF: sententialForm a b) = newSF: (sententialForm a b) {exists rule. (List.Tot.mem rule ruleList /\ rewrite oldSF rule = newSF)}
	type lderType (a: eqtype) (b: eqtype) (ruleList: list (rule a b)) (oldSF: sententialForm a b) = newSF: (sententialForm a b) {lderives a b ruleList oldSF newSF}
	type lderSeqType (a: eqtype) (b: eqtype) (ruleList: list (rule a b)) = listSF: list (sententialForm a b) {lderivesSeq a b ruleList listSF}


	val getStartNonterm: #a:eqtype -> #b:eqtype -> list (rule a b) -> Tot (sententialForm a b)
	let getStartNonterm #a #b rl = 
		let st = List.Tot.filter (fun rule -> rule.isStart) rl in
		if is_Cons st then [PRef((List.Tot.hd st).name, None)] else [PRef (new_Source0 "S", None)]


	val listLast: #a:Type -> l: list a {is_Cons l} -> Tot a
	let rec listLast #a l = 
		match l with 
		| h1::h2::tl -> listLast (h2::tl)
		| hd::tl -> hd




(*
//Ok
	val str1: sententialForm source source
	let str1 = [PRef (new_Source0 "S", None)]

	val str11: lderType source source (Helpers.lift cbs) str1
	let str11 = [PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")")]

	val str12: lderType source source (Helpers.lift cbs) str1
	let str12 = [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]

	val str13: lderType source source (Helpers.lift cbs) str1
	let str13 = []
*)






	
	//val d3: lderType source source (Helpers.lift cbs) d2
	val d3: sententialForm source source
	let d3 = [PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")"); PRef (new_Source0 "S", None)]
	
	//val d4: lderType source source (Helpers.lift cbs) d3
	val d4: sententialForm source source
	let d4 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PRef (new_Source0 "S", None)]
	
	//val d5: lderType source source (Helpers.lift cbs) d4
	val d5: sententialForm source source
	let d5 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")")]
	
	//val d6: lderType source source (Helpers.lift cbs) d5
	val d6: sententialForm source source
	let d6 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")"); PToken (new_Source0 ")")]
	
	//val d7: lderType source source (Helpers.lift cbs) d6
	val d7: sententialForm source source
	let d7 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 ")")]



	//val dl7: lderSeqType source source (Helpers.lift cbs)
	//let dl7 = 
	//	assert (lderivesSeq source source (Helpers.lift cbs) [d1; d2; d3; d4; d5] ) ;
	//	assert (lderivesSeq source source (Helpers.lift cbs) [d3; d4; d5; d6; d7] ) ;
	//	[d1; d2; d3; d4; d5; d6; d7]


	


(*
//for lulz 

	val rewriteRL: #a:eqtype -> #b:eqtype -> list (rule a b) -> sententialForm a b -> Tot (list (sententialForm a b))
	let rewriteRL #a #b ruleList sf =
		List.Tot.flatten (List.Tot.map (rewrite sf) ruleList)


	let bind sfl f = List.Tot.flatten (List.Tot.map f sfl)

*)



(*	//alternative def
	type language (a:eqtype) (b:eqtype) (ruleList: list (rule a b)) = 
		lang: list (sentence a b) {forall sent. List.Tot.mem sent lang ==> lderives ruleList (getStartNonterm ruleList) sent}
*) 

	type language (a:eqtype) (b:eqtype) (ruleList: list (rule a b)) = 
		word: (sentence a b) { exists (seq: lderSeqType a b ruleList). is_Cons seq /\ List.Tot.hd seq = getStartNonterm ruleList /\ listLast seq = word }





	//val ts: language source source (Helpers.lift cbs)
	//let ts =
	//	assert (lderivesSeq source source (Helpers.lift cbs) [d1; d2; d3; d4; d5; d6; d7] ) ;
	//	[PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 ")")]


(*
//
    val tsL: #a:eqtype -> #b:eqtype 
        -> ruleList:list (rule a b) -> 
        Lemma 
            (requires (ruleList: list (rule a b) {forall rule0. List.Tot.mem rule0 ruleList ==> isNotEpsRule rule0}))
            (ensures (List.Tot.isEmpty (getEpsRuleNameList ruleList)))

    let rec tsL #a #b ruleList = 
        match ruleList with  
        | [] -> ()
        | hd::tl -> epsGenLemma1 tl
*)


	assume val compose: #a:Type -> #b:Type -> list (rule a b) -> Tot (rule a b)
	assume val subset: #a:Type -> list a -> list a -> Tot bool
	assume val alphabet: #a:Type -> #b:Type -> list (rule a b) -> Tot (list (sententialForm a b))

    assume val subLangTheorem: #a:eqtype -> #b:eqtype -> rl1: list (rule a b) -> rl2: list (rule a b)
        -> Lemma 
            (requires True) 
            (ensures ( 
            	
            	(forall (x: language a b rl1). exists (y: language a b rl2). x = y) <==> // X in Y
            		
            		( forall rule1. List.Tot.mem rule1 rl1 ==> 

            			(exists sub_rl2. subset sub_rl2 rl2 /\ 
            				(forall term. List.Tot.mem term (alphabet rl1) ==> (rewrite term rule1 = rewrite term (compose sub_rl2))          )          
            				
            			)


            				)



            	)
            )



	val nth: #a:eqtype -> l: list a -> (ind: nat {ind < List.Tot.length l}) -> Tot a
	let rec nth #a l n = match l with
		| hd::tl -> if n = 0 then hd else nth tl (n - 1)

(*

    val lemma0: 
		x: language source source (Helpers.lift cbs)
        -> Lemma 
            (requires True) 
            (ensures ( exists (y: language source source (SplitLongRule.splitLongRule cbs)). x = y ))
    let lemma0 x =

		let oldCbs = Helpers.lift cbs in 
		let newCbs = SplitLongRule.splitLongRule cbs in
		let snOldCbs = getStartNonterm oldCbs in
		let snNewCbs = getStartNonterm newCbs in

		assume (List.Tot.length oldCbs = 3);
		assume (List.Tot.length newCbs = 4);

    	let r1 = nth oldCbs 0 in 
    	let r2 = nth oldCbs 1 in 
    	let r3 = nth oldCbs 2 in 

	   	let nr1 = nth newCbs 0 in 
    	let nr2 = nth newCbs 1 in 
    	let nr3 = nth newCbs 2 in 
    	let nr4 = nth newCbs 3 in 

    	
    	assume (forall (x: sententialForm source source). (forall t. List.Tot.mem t x ==> List.Tot.mem t (termCbs @ nonTermCbs)) /\ rewrite x r1 = rewrite (rewrite x nr1) nr2 );
    	assume (forall (x: sententialForm source source). rewrite x r2 = rewrite x nr3);
    	assume (forall (x: sententialForm source source). rewrite x r3 = rewrite x nr4);



		assert ( exists seq. is_Cons seq /\ List.Tot.hd seq = snOldCbs /\ listLast seq = x );

		assume ( 


			(exists (seq: lderSeqType source source oldCbs). is_Cons seq /\ List.Tot.hd seq = snOldCbs /\ listLast seq = x) ==> 
				(exists (seq: lderSeqType source source newCbs). is_Cons seq /\ List.Tot.hd seq = snNewCbs /\ listLast seq = x)


			);



    	assume (exists (y: language source source newCbs). x = y );
    	assert (exists (y: language source source newCbs). x = y );

    	()




*)



	let main = 
		"> " ^ (Printer.printListRule old_cbs) ^ "\n\n" ^ (Printer.printListRule new_cbs)

 	
(*
    val lemma0: 
		x: language source source (Helpers.lift cbs)
        -> Lemma 
            (requires True) 
            (ensures ( exists (y: language source source (SplitLongRule.splitLongRule cbs)). x = y ))
    let rec lemma0 x = match x with
    	| [] -> admit()

(*
	    	let oldCbs = Helpers.lift cbs in 
	    	let newCbs = SplitLongRule.splitLongRule cbs in
    		let snOldCbs = getStartNonterm oldCbs in
    		let snNewCbs = getStartNonterm newCbs in
*)

(*
    		assert ( List.Tot.length newCbs = 4 );
    		let nr4 = nth newCbs 3 in 
    		let d1 = snNewCbs in
    		assert ( d1 = [PRef (new_Source0 "S", None)] );
    		let (d2: sentence source source) = [] in
    		assert (d2 = []);
    		let seq = [d1;d2] in
*)

(*
    		let (seq: lderSeqType source source newCbs) = [] in
    		let (y: sentence source source) = [] in


    		assume (is_Cons seq);
    		assume (List.Tot.hd seq = snNewCbs);
    		assume (listLast seq = y);
    		assert (exists (y: language source source newCbs). x = y);

    		()
*)
//fail
    	| hd::tl -> 

    		//assume (tl << x); 

    		assert (tl << x) ;


    		admit ()
    		//lemma0 tl
*)


(*
    val lemma0: 
		u:unit
        -> Lemma 
            (requires True) 
            (ensures ( forall (x: language source source (Helpers.lift cbs)). exists (y: language source source (SplitLongRule.splitLongRule cbs)). x = y ))
    let lemma0 () = 


    	let oldCbs = Helpers.lift cbs in 
    	let newCbs = SplitLongRule.splitLongRule cbs in


    	let snOldCbs = getStartNonterm oldCbs in
    	let snNewCbs = getStartNonterm newCbs in


    	assert ( snOldCbs = snNewCbs );


    	assert ( List.Tot.length cbs = 3 );
    	assert ( List.Tot.length ncbs = 4 );


    	let r1 = nth cbs 0 in 
    	let r2 = nth cbs 1 in 
    	let r3 = nth cbs 2 in 

    	let nr1 = nth ncbs 0 in 
    	let nr2 = nth ncbs 1 in 
    	let nr3 = nth ncbs 2 in 
    	let nr4 = nth ncbs 3 in 

    	
    	//assume (forall (x: sententialForm source source). (forall t. List.Tot.mem t x ==> List.Tot.mem t (termCbs @ nonTermCbs)) /\ rewrite x r1 = rewrite (rewrite x nr1) nr2 );
    	//assume (forall (x: sententialForm source source). rewrite x r2 = rewrite x nr3);
    	//assume (forall (x: sententialForm source source). rewrite x r3 = rewrite x nr4);

//		type language source source oldCbs = 
//			word: (sentence source source) { exists (seq: lderSeqType source source oldCbs). is_Cons seq /\ List.Tot.hd seq = snOldCbs /\ listLast seq = word }

//		type language source source newCbs = 
//			word: (sentence source source) { exists (seq: lderSeqType source source newCbs). is_Cons seq /\ List.Tot.hd seq = snNewCbs /\ listLast seq = word }




    	//assert ( forall (x: language source source oldCbs). exists (y: language source source newCbs). x = y );

    	()


		
		assert (forall (x:nat). exists (y:nat). x + x = y);

		admit()
*)


(*
    val lemma0: 
		x: language source source (Helpers.lift cbs)
        -> Lemma 
            (requires True) 
            (ensures ( exists (y: language source source (SplitLongRule.splitLongRule cbs)). x = y ))
    let lemma0 x = 


    	let oldCbs = Helpers.lift cbs in 
    	let newCbs = SplitLongRule.splitLongRule cbs in


    	let snOldCbs = getStartNonterm oldCbs in
    	let snNewCbs = getStartNonterm newCbs in


    	assert ( snOldCbs = snNewCbs );


    	assert ( List.Tot.length oldCbs = 3 );
    	assert ( List.Tot.length newCbs = 4 );


    	//let r1 = nth cbs 0 in 
    	//let r2 = nth cbs 1 in 
    	//let r3 = nth cbs 2 in 

    	//let nr1 = nth ncbs 0 in 
    	//let nr2 = nth ncbs 1 in 
    	//let nr3 = nth ncbs 2 in 
    	//let nr4 = nth ncbs 3 in 

    	
    	//assume (forall (x: sententialForm source source). (forall t. List.Tot.mem t x ==> List.Tot.mem t (termCbs @ nonTermCbs)) /\ rewrite x r1 = rewrite (rewrite x nr1) nr2 );
    	//assume (forall (x: sententialForm source source). rewrite x r2 = rewrite x nr3);
    	//assume (forall (x: sententialForm source source). rewrite x r3 = rewrite x nr4);

//		type language source source oldCbs = 
//			word: (sentence source source) { exists (seq: lderSeqType source source oldCbs). is_Cons seq /\ List.Tot.hd seq = snOldCbs /\ listLast seq = word }

//		type language source source newCbs = 
//			word: (sentence source source) { exists (seq: lderSeqType source source newCbs). is_Cons seq /\ List.Tot.hd seq = snNewCbs /\ listLast seq = word }


		
		//assert (forall (x:nat). exists (y:nat). x + x = y);
		assume ( exists (y: sentence source source). exists (seq: lderSeqType source source newCbs). is_Cons seq /\ List.Tot.hd seq = snNewCbs /\ listLast seq = y /\ x = y );

		assert ( exists (y: language source source newCbs). x = y );
		admit()
*)


(*



    	let snOldCbs = getStartNonterm oldCbs in
    	let snNewCbs = getStartNonterm newCbs in


    	assert ( snOldCbs = snNewCbs );


    	assert ( List.Tot.length oldCbs = 3 );
    	assert ( List.Tot.length newCbs = 4 );


    	//let r1 = nth cbs 0 in 
    	//let r2 = nth cbs 1 in 
    	//let r3 = nth cbs 2 in 

    	//let nr1 = nth ncbs 0 in 
    	//let nr2 = nth ncbs 1 in 
    	//let nr3 = nth ncbs 2 in 
    	//let nr4 = nth ncbs 3 in 

    	
    	//assume (forall (x: sententialForm source source). (forall t. List.Tot.mem t x ==> List.Tot.mem t (termCbs @ nonTermCbs)) /\ rewrite x r1 = rewrite (rewrite x nr1) nr2 );
    	//assume (forall (x: sententialForm source source). rewrite x r2 = rewrite x nr3);
    	//assume (forall (x: sententialForm source source). rewrite x r3 = rewrite x nr4);

//		type language source source oldCbs = 
//			word: (sentence source source) { exists (seq: lderSeqType source source oldCbs). is_Cons seq /\ List.Tot.hd seq = snOldCbs /\ listLast seq = word }

//		type language source source newCbs = 
//			word: (sentence source source) { exists (seq: lderSeqType source source newCbs). is_Cons seq /\ List.Tot.hd seq = snNewCbs /\ listLast seq = word }


		
		//assert (forall (x:nat). exists (y:nat). x + x = y);
		assume ( exists (y: sentence source source). exists (seq: lderSeqType source source newCbs). is_Cons seq /\ List.Tot.hd seq = snNewCbs /\ listLast seq = y /\ x = y );

		assert ( exists (y: language source source newCbs). x = y );
		admit()
*)