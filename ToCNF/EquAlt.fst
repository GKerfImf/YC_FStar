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

    val start_symbol_old_cbs: production source source
    let start_symbol_old_cbs = PRef (new_Source0 "S", None)

	val old_cbs: list ( rule0: (rule source source))
	let old_cbs = [Helpers.simpleStartRule "S" (List.Tot.map create [PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")")]);
	    Helpers.simpleNotStartRule "S" (List.Tot.map create [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]);
	    Helpers.simpleNotStartRule "S" (List.Tot.map create [])]


    val start_symbol_new_cbs: production source source
    let start_symbol_new_cbs = PRef (new_Source0 "S", None)

	val new_cbs: list (rule source source) 
	let new_cbs = SplitLongRule.splitLongRule old_cbs

//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

	type rule_in (#a:eqtype) (#b:eqtype) (g: list (rule a b)) = r : (rule a b) {exists r2. List.Tot.mem r2 g /\ r2 = r} 

	val start_symbol: #a:eqtype -> #b:eqtype -> list (rule a b) -> Tot (production a b)
	let start_symbol #a #b g = PRef (new_Source0 "S", None)


	val getProds: #a:eqtype -> #b:eqtype -> rule a b -> Tot (list (production a b))
	let getProds #a #b rule = match rule.body with
		| PSeq(els,_,_) -> List.Tot.map (fun elem -> elem.rule) els
		| _ -> []

	val left: #a:eqtype -> #b:eqtype -> rule a b -> Tot (production a b)
	let left #a #b rule = PRef (rule.name, None) 

	val rigth: #a:eqtype -> #b:eqtype -> r: rule a b -> Tot (list (production a b))
	let rigth #a #b rule = getProds rule 


	type derives (#a:eqtype) (#b:eqtype) (g: list (rule a b)) (old_sf: sententialForm a b) (new_sf: sententialForm a b) =
		| DerivesRefl: 
			   sf1: sententialForm a b { sf1 = old_sf /\ sf1 = new_sf }
			-> derives g old_sf new_sf
		| DerivesStep: 
			   sf1: sententialForm a b
			-> sf2: sententialForm a b 
			-> r: (rule_in g) {sf1 @ (rigth r) @ sf2 = new_sf }
			-> derives g old_sf (sf1 @ [left r] @ sf2)
			-> derives g old_sf new_sf



	//val d1: sententialForm source source
	//let d1 = [PRef (new_Source0 "S", None)]

	val d2: sententialForm source source
	let d2 = [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]
	
	val d3: sententialForm source source
	let d3 = [PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")"); PRef (new_Source0 "S", None)]
	
	val d4: sententialForm source source
	let d4 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PRef (new_Source0 "S", None)]
	
	val d5: sententialForm source source
	let d5 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")")]
	
	val d6: sententialForm source source
	let d6 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")"); PToken (new_Source0 ")")]
	
	val d7: sententialForm source source
	let d7 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 ")")]





	val nth: #a:eqtype -> l: list a -> (ind: nat {ind < List.Tot.length l}) -> Tot a
	let rec nth #a l n = match l with
		| hd::tl -> if n = 0 then hd else nth tl (n - 1)



//Test
	val d_d1_d7: derives old_cbs [start_symbol_old_cbs] d7
	let d_d1_d7 = 
		assert (List.Tot.length old_cbs = 3);

		let rule0 = nth old_cbs 0 in
		let rule1 = nth old_cbs 1 in
		let rule2 = nth old_cbs 2 in

		let (der1: derives old_cbs [start_symbol_old_cbs] [start_symbol_old_cbs]) = DerivesRefl [start_symbol_old_cbs] in
		let (der2: derives old_cbs [start_symbol_old_cbs] d2) = DerivesStep [] [] rule1 der1 in
		let (der3: derives old_cbs [start_symbol_old_cbs] d3) = 
			let sf1 = [] in
			let sf2 = [PRef (new_Source0 "S", None)] in
			assert (sf1 @ [left rule0] @ sf2 = d2);
			assert (sf1 @ (rigth rule0) @ sf2 = d3);
			DerivesStep sf1 sf2	rule0 der2 in 

		let (der4: derives old_cbs [start_symbol_old_cbs] d4) = 
			let sf1 = [PToken (new_Source0 "(")] in
			let sf2 = [PToken (new_Source0 ")"); PRef (new_Source0 "S", None)] in
			assert (sf1 @ [left rule2] @ sf2 = d3);
			assert (sf1 @ (rigth rule2) @ sf2 = d4);
			DerivesStep sf1 sf2	rule2 der3 in 

		let (der5: derives old_cbs [start_symbol_old_cbs] d5) = 
			let sf1 = [PToken (new_Source0 "("); PToken (new_Source0 ")")] in
			let sf2 = [] in
			assert (sf1 @ [left rule0] @ sf2 = d4);
			assert (sf1 @ (rigth rule0) @ sf2 = d5);
			DerivesStep sf1 sf2	rule0 der4 in 

		let (der6: derives old_cbs [start_symbol_old_cbs] d6) = 
			let sf1 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "(")] in
			let sf2 = [PToken (new_Source0 ")")] in
			assert (sf1 @ [left rule0] @ sf2 = d5);
			assert (sf1 @ (rigth rule0) @ sf2 = d6);
			DerivesStep sf1 sf2	rule0 der5 in 

		let (der7: derives old_cbs [start_symbol_old_cbs] d7) = 
			let sf1 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PToken (new_Source0 "(")] in
			let sf2 = [PToken (new_Source0 ")"); PToken (new_Source0 ")")] in
			assert (sf1 @ [left rule2] @ sf2 = d6);
			assert (sf1 @ (rigth rule2) @ sf2 = d7);
			DerivesStep sf1 sf2	rule2 der6 in 

		der7



	val eq_f: sf:sententialForm source source -> derives old_cbs [start_symbol_old_cbs] sf -> derives new_cbs [start_symbol_new_cbs] sf
	let rec eq_f sf der = 
		match der with
		| DerivesRefl sf -> 
			assert (sf = [start_symbol_old_cbs]);
			assert ([start_symbol_new_cbs] = [start_symbol_old_cbs]);
			assert ([start_symbol_new_cbs] = sf);
			let (newder: derives new_cbs [start_symbol_new_cbs] sf) = DerivesRefl sf in
			newder

		| DerivesStep sf1 sf2 rule s_der -> 

			assert (List.Tot.length old_cbs = 3);

			let old_rule0 = nth old_cbs 0 in
			let old_rule1 = nth old_cbs 1 in
			let old_rule2 = nth old_cbs 2 in


			assert (List.Tot.length new_cbs = 4);

			let new_rule0 = nth new_cbs 0 in
			let new_rule1 = nth new_cbs 1 in
			let new_rule2 = nth new_cbs 2 in
			let new_rule3 = nth new_cbs 3 in


			let (newder: derives new_cbs [start_symbol_new_cbs] sf) = 

				if rule = old_rule0 then
					begin

						let (temp2: derives new_cbs [start_symbol_new_cbs] (sf1 @ [left new_rule0] @ sf2) ) = eq_f (sf1 @ [left new_rule0] @ sf2) s_der in
						let (temp3: derives new_cbs [start_symbol_new_cbs] (sf1 @ (rigth new_rule0) @ sf2) ) = DerivesStep sf1 sf2 new_rule0 temp2 in

						let (temp4: derives new_cbs [start_symbol_new_cbs] sf) = 

							let sf1n = sf1 @ [PToken (new_Source0 "(") ] in

							assume (sf1n @ [left new_rule1] @ sf2 = sf1 @ (rigth new_rule0) @ sf2 );
							assume (sf1n @ (rigth new_rule1) @ sf2 = sf);
												
							DerivesStep (sf1n) sf2 new_rule1 temp3 in

	                	temp4

                	end

               	else if rule = old_rule1 then
               		begin
               			assert (rule = old_rule1);
	               		assert (old_rule1 = new_rule2);

						let (temp1: derives new_cbs [start_symbol_new_cbs] (sf1 @ [left new_rule2] @ sf2)) = eq_f (sf1 @ [left new_rule2] @ sf2) s_der in
	                	DerivesStep sf1 sf2 new_rule2 temp1
                	end

                else 
                	begin
                		assert (rule = old_rule2);
						assert (old_rule2 = new_rule3);

						let (temp1: derives new_cbs [start_symbol_new_cbs] (sf1 @ [left new_rule3] @ sf2)) = eq_f (sf1 @ [left new_rule3] @ sf2) s_der in
	                	DerivesStep sf1 sf2 new_rule3 temp1
                	end
                in

			newder



	type generates (#a:eqtype) (#b:eqtype) (g: list (rule a b)) = sf: sententialForm a b {derives g [start_symbol g] sf} 

	val sf_d7: generates old_cbs 
	let sf_d7 = d7


	type produces (#a:eqtype) (#b:eqtype) (g: list (rule a b)) = sf: sentence a b { generates g } 

	val s_d7: produces old_cbs 
	let s_d7 = d7


	//TODO: del
	let rec concat l = match l with | [] -> "" | x::xs -> x ^ " " ^ concat xs 

	val printer: a:sententialForm source source -> b:sententialForm source source -> cbs: list (rule source source) -> derives cbs a b -> string
	let rec printer a b cbs der = 
		(b |> List.Tot.collect (fun el -> match el with | PRef(s,_) | PToken(s) -> [s.text] | _ -> [])  |> concat) ^ 
		
		(match der with 
		| DerivesRefl sf -> ""
		| DerivesStep sf1 sf2 rule sder -> "\n" ^ printer a (sf1 @ [left rule] @ sf2) cbs sder)



	let main = 
		//assume (new_cbs = new_cbs1); 
		//"> " ^ (Printer.printListRule old_cbs) ^ "\n\n" ^ (Printer.printListRule new_cbs) ^ "\n\n" ^ (Printer.printListRule new_cbs1) 


		"> " ^ (printer [start_symbol_old_cbs] d7 old_cbs d_d1_d7) ^ "\n\n" ^ 

		"> " ^ (printer [start_symbol_new_cbs] d7 new_cbs (eq_f d7 d_d1_d7))

