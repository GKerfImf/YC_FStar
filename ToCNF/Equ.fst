module Equ
	open FStar.IO
	open IL
	open Yard.Core.Conversions


	type sentence (patt:eqtype) (expr:eqtype) = terms: list (production patt expr){forall prod. List.Tot.mem prod terms ==> Helpers.isPToken prod}
	type sententialForm (patt:Type) (expr:Type) = list (production patt expr)



	//val isSentence: #a:eqtype -> #b:eqtype -> list (production a b) -> Tot bool
	//let isSentence #a #b prodList = 
	//	List.Tot.for_all Helpers.isPToken prodList


//TODO: move to Helpers 
    val create: 
         production 'a 'b -> Tot (elem 'a 'b)
    let create arule = {omit=false; binding=None; checker=None; rule = arule}


	val test: list (rule0: (rule source source) {Helpers.isPSeq rule0.body}) 
	let test = [Helpers.simpleStartRule "S" (List.Tot.map create [PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")")]);
	    Helpers.simpleNotStartRule "S" (List.Tot.map create [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]);
	    Helpers.simpleNotStartRule "S" (List.Tot.map create [])]

	val cbs: list (rule source source)
	let cbs = Helpers.lift test


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

	val str11: lderType source source cbs str1
	let str11 = [PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")")]

	val str12: lderType source source cbs str1
	let str12 = [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]

	val str13: lderType source source cbs str1
	let str13 = []
*)



	val d1: sententialForm source source
	let d1 = [PRef (new_Source0 "S", None)]

	//val d2: lderType source source cbs d1
	val d2: sententialForm source source
	let d2 = [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]
	
	//val d3: lderType source source cbs d2
	val d3: sententialForm source source
	let d3 = [PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")"); PRef (new_Source0 "S", None)]
	
	//val d4: lderType source source cbs d3
	val d4: sententialForm source source
	let d4 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PRef (new_Source0 "S", None)]
	
	//val d5: lderType source source cbs d4
	val d5: sententialForm source source
	let d5 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")")]
	
	//val d6: lderType source source cbs d5
	val d6: sententialForm source source
	let d6 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PToken (new_Source0 "("); PRef (new_Source0 "S", None); PToken (new_Source0 ")"); PToken (new_Source0 ")")]
	
	//val d7: lderType source source cbs d6
	val d7: sententialForm source source
	let d7 = [PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 ")")]



	val dl7: lderSeqType source source cbs
	let dl7 = 
		assert (lderivesSeq source source cbs [d1; d2; d3; d4; d5] ) ;
		assert (lderivesSeq source source cbs [d3; d4; d5; d6; d7] ) ;
		[d1; d2; d3; d4; d5; d6; d7]


	


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


	val ts: language source source cbs
	let ts =
		assert (lderivesSeq source source cbs [d1; d2; d3; d4; d5; d6; d7] ) ;
		[PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 "("); PToken (new_Source0 "("); PToken (new_Source0 ")"); PToken (new_Source0 ")")]


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


(*

//exists (seq: lderSeqType a b ruleList). is_Cons seq /\ List.Tot.hd seq = getStartNonterm ruleList /\ listLast seq = sent 

	val noname: a:eqtype -> b:eqtype -> rl:list (rule a b) -> sent: sentence a b -> Tot bool	
	let noname a b rl sent = 
		true



	//type language (a:eqtype) (b:eqtype) (ruleList: list (rule a b)) = 
	//	lang: list (sentence a b) {forall sent. List.Tot.mem sent lang ==> lderives ruleList (getStartNonterm ruleList) sent}

	type lang (a:eqtype) (b:eqtype) (ruleList: list (rule a b)) = 
		sent: (sentence a b) { noname a b ruleList sent }

	val ts: lang source source (Helpers.lift test)
	let ts = [PToken (new_Source0 "("); PToken (new_Source0 ")")]

*)


	//assume val transformation: #a:eqtype -> #b:eqtype
	//	-> list (rule a b) -> Tot (list (rule a b))

    //assume val lemma0: 
    //	#a:eqtype -> #b:eqtype
	//	-> ruleList: list (rule a b) -> l1: language a b ruleList -> l2: language a b (transformation ruleList)
    //    -> Lemma 
    //        (requires True) 
    //        (ensures (forall x. List.Tot.mem x l1 ==> List.Tot.mem x l2)) 

    //assume val lemma1: 
    //	#a:eqtype -> #b:eqtype
	//	-> ruleList: list (rule a b) -> l1: language a b ruleList -> l2: language a b (transformation ruleList)
    //    -> Lemma 
    //        (requires True) 
    //        (ensures (forall x. List.Tot.mem x l2 ==> List.Tot.mem x l1)) 

		


    let rec concat l = match l with | [] -> "" | x::xs -> x ^ " " ^ concat xs 

    let getText = function 
    	| PToken(s) | PRef (s,_) -> s.text
        | _ -> ""

    let printruleBody ruleSeq = ruleSeq |> List.Tot.map getText |> concat

	let rec printListBodys = function 
		| [] -> "" 
		| hd::tl -> printruleBody hd  ^ "\n" ^ printListBodys tl



	let main = 
		"> " //^ printListBodys [d7]


 	

