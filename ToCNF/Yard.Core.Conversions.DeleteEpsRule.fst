module Yard.Core.Conversions.DeleteEpsRule
    open IL
    open Yard.Core
    open Yard.Core.Conversions
    open FStar.ListProperties
    open TransformAux
    
	
// -- Функция для удаления эпсилон-правил-----------------------------------------------------------

    val listfromto_acc: a:int {a >= 1} -> b:int {b >= a} -> list int -> Tot (list int)
    let rec listfromto_acc a b acc =
        if (a = b) then List.Tot.append [a] acc
        else listfromto_acc a (b - 1) (List.Tot.append [b] acc)

    // a, b ~~> [a, a+1, ..., b]
    val listfromto: a:int {a >= 1} -> b:int {b >= a} -> Tot (list int)
    let listfromto a b = listfromto_acc a b []

    // X:List --> 2^X
    val powerset: list int -> Tot (res: list (list int){is_Cons res})
    let rec powerset =
        function
        | [] -> [[]]
        | x::xs -> List.Tot.collect (fun subset -> [subset; List.Tot.append [x] subset]) (powerset xs)

    // n ~~> 2^[1..n] \ []
    val genSubsets: n: int {n >= 1} -> Tot (list (list int))
    let genSubsets n = List.Tot.tl (powerset (listfromto 1 n))

    // if (A => eps) then true
    val isEpsRule: Rule 'a 'b -> Tot bool 
    let isEpsRule rule = 
        match rule.body with
        | PSeq(elements, _, _) -> List.isEmpty elements
        | _ -> false

    // ruleList -> [Ai => eps]
    val epsRuleNameList: list (Rule 'a 'b) -> Tot (list string)
    let epsRuleNameList ruleList = 
        List.Tot.collect (fun rule -> if (isEpsRule rule) then [rule.name.text] else []) ruleList

    // (A -> BCD) ~> ["B";"C";"D"]
    val ruleNontermNameList: Rule 'a 'b -> Tot (list string)
    let ruleNontermNameList rule = 
        match rule.body with
        | PRef(s,_) -> [s.text]
        | PSeq(elements,_,_) -> List.Tot.collect (fun elem -> match elem.rule with PRef(s,_) -> [s.text] | _ -> []) elements
        | _ -> []

    // ? A => C1,...,Cn where forall i in [1..n] : Ci => eps
    val isEpsWeakGenerating: Rule 'a 'b -> list string -> Tot bool
    let isEpsWeakGenerating rule epsNameList =
        match rule.body with
        | PSeq(elements,_,_) -> 
            List.Tot.for_all (fun elem -> match elem.rule with PRef(s,_) -> List.Tot.contains s.text epsNameList | _ -> false ) elements
        | _ -> false



    assume val epsGeneratingHelper: list (Rule 'a 'b)  -> list string -> Tot (list string) 
(*    val epsGeneratingHelper: list (Rule 'a 'b)  -> list string -> Tot (list string) (decreases %[ TransformAux.lengthBodyRule rule])
    let rec epsGeneratingHelper ruleList epsGenNameList =
        let newEpsGenNameList = 
            ruleList 
            |> List.filter (fun rule -> isEpsWeakGenerating rule epsGenNameList)
            |> List.map (fun rule -> rule.name.text) in 
        if (newEpsGenNameList = epsGenNameList) then epsGenNameList
        else epsGeneratingHelper ruleList newEpsGenNameList 
*)
    // ruleList -> [Ai =>* eps]
    val epsGeneratingNameList: list (Rule 'a 'b) ->  (list string)
    let epsGeneratingNameList ruleList =
        epsGeneratingHelper ruleList (epsRuleNameList ruleList)
//******************************************************************************************************************



(*	
	val newBodyCreateElem: elem 'a 'b -> int -> list (Rule 'a 'b) -> Tot (list (elem 'a 'b))
	let newBodyCreateElem elem i ruleList =
		match elem.rule with
		| PRef(t, _) ->
			if not (List.Tot.isEmpty (isEpsName t.text ruleList))
			then [TransformAux.createSimpleElem (PRef(new_Source0(string_of_int i), None)) elem.binding]
			else [elem]	
		| _ -> [elem]
*)

(*		
	val newBody: list (elem 'a 'b) -> int -> list (Rule 'a 'b) -> Tot (list (elem 'a 'b))
	let rec newBody elements i ruleList =
		match elements with 
		| [] -> []
		| hd::tl -> List.Tot.append (newBodyCreateElem hd i ruleList) (newBody tl (i + 1) ruleList)			
*)

(*
    val nth: list 'a -> int -> Tot (option 'a)
    let rec nth l n = match l with
      | []     -> None
      | hd::tl -> if n = 0 then Some hd 
                  else if n < 0 then None else nth tl (n - 1)
*)                  
(*	  
	val addRule: Rule 'a 'b -> list string -> list int -> Tot (list (Rule 'a 'b))
	let addRule numberRule epsRef eps =
		let epsWithNameExists t =
			let epsMap = List.Tot.map string_of_int eps in
				List.Tot.existsb (fun x -> x = t) epsMap
			in
			
		let newBody = List.Tot.collect
			(fun elem ->
				match elem.rule with
				| PRef(t,_) ->
					if (epsWithNameExists t.text) then []
					else 
						if (fst (int32_tryParse t.text))
						then 
							(match (nth epsRef (snd (int32_tryParse t.text) - 1)) with 
							| Some x -> [TransformAux.createSimpleElem (PRef(new_Source0(x), None)) elem.binding]
							| None -> [])
						else [elem]																													
				| _ -> [elem]
			) (match numberRule.body with PSeq(e, a, l) -> e | _ -> []) in 
			
		let ac,lbl = match numberRule.body with PSeq(e, a, l) -> a,l | _ -> None,None in			
		[{numberRule with body=PSeq(newBody, ac, lbl)}]
*)

(*
	val numberBody: Rule 'a 'b -> 	list (Rule 'a 'b) -> Tot (Production 'a 'b)
	let numberBody rule ruleList =
		let ac, lbl = match rule.body with PSeq(e, a, l) -> a,l | x -> None,None in
			match rule.body with
			|PSeq(elements, _, _) -> PSeq(newBody elements 0 ruleList, ac, lbl)
			|_ -> rule.body
*)
(*		 
	val newRule: Rule 'a 'b 
        -> list string 
        -> list (Rule 'a 'b) 
        -> Tot (list (Rule 'a 'b))
    let newRule rule epsRef ruleList =
        if not (List.Tot.isEmpty epsRef) then
            let numberEpsRef = genSubsets (List.Tot.length epsRef) in
            let numberRule = {rule with body = numberBody rule ruleList} in
            List.Tot.collect (addRule numberRule epsRef) numberEpsRef
        else [] 
(*
*)
	val newRules: list (Rule 'a 'b) 
		-> Tot (list (Rule 'a 'b))
	let newRules ruleList = 
		List.Tot.collect
				(fun rule ->
					match rule.body with
					| PSeq(elements, _, _) ->
						if not (List.Tot.isEmpty elements) 
						then List.Tot.append (newRule rule (epsInRule elements ruleList) ruleList) [rule]
						else []
					| _ -> []
				) ruleList
*)
(*	
	val trashFilter: Rule 'a 'b -> Tot bool
	let trashFilter rule =
		let elements = match rule.body with PSeq(e, _, _) -> e | _ -> [] in
		if List.Tot.length elements = 1 then 
			match (List.Tot.hd elements).rule with
			| PRef (e,_) -> not (rule.name.text = e.text)
			| _ -> true
		else true
*)
(*	
	// Удаление правил вида A -> A
	val deleteTrashRule: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
	let deleteTrashRule rulesList = 
		List.Tot.filter(fun rule -> trashFilter rule) rulesList
*)
(*
    // TODO: доказать progress: в результате нет eps-правил
	val deleteEpsRule: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
    let deleteEpsRule ruleList =
        let listNewRules = newRules ruleList in
        let nonemptyRules = List.Tot.filter (fun r -> match r.body with PSeq([],_,_) -> false | _ -> true) listNewRules in 
        deleteTrashRule nonemptyRules
*)
(*
    //val deleteEpsRule: 
    //    ruleList : 
    //    	list (Rule 'a  'b) 
    //    	-> Tot (result:(list (Rule 'a 'b)){List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) result} ) (decreases %[ TransformAux.lengthBodyRule rule])
*)

// TODO: Доказать полиномиальность для коротких правил