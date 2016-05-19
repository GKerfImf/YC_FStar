module Yard.Core.Conversions.DeleteEpsRule
    open IL
    open Yard.Core.Conversions
	open FStar.ListProperties
	open TransformAux
	
// -- Функция для удаления эпсилон-правил-----------------------------------------------------------

    assume val int32_tryParse : string -> Tot (bool * int)
	
	val listfromto_acc: a:int {a >= 1} -> b:int {b >= a} -> list int -> Tot (list int)
	let rec listfromto_acc a b acc =
		if (a = b) then List.Tot.append [a] acc
		else listfromto_acc a (b - 1) (List.Tot.append [b] acc)

	val listfromto: a:int {a >= 1} -> b:int {b >= a} -> Tot (list int)
	let listfromto a b = listfromto_acc a b []
		
	val powerset: (list int -> Tot (list (list int)))
	let rec powerset =
		function
		| [] -> [[]]
		| x::xs -> List.Tot.collect (fun subset -> [subset; List.Tot.append [x] subset]) (powerset xs)

	//--Powerset [1..N]
	val genSubsets: n: int {n >= 1} -> Tot (list (list int))
	let genSubsets n = powerset (listfromto 1 n)
		
	// Список всех правил
	val epsList: list (Rule 'a  'b) -> Tot (list string)
	let epsList ruleList = 
		List.Tot.collect
			(fun rule -> 
				match rule.body with
				| PSeq(elements, actionCode, lbl) -> 
					if List.Tot.isEmpty elements then [rule.name.text] else []
				| _ -> []
			) ruleList

	//-- Проверка вхождения эпсилон-правила
	val isEps: string -> list (Rule 'a  'b) -> Tot (list string)
	let isEps s ruleList = List.Tot.filter (fun x -> x = s) (epsList ruleList)

	//-- Список эпсилон-правил входящих в данное правило
	assume val epsInRule: listEls: list (elem 'a 'b) -> list (Rule 'a  'b) -> Tot (list string) //(decreases %[TransformAux.heightBodyEls listEls])
	(*let rec epsInRule elements ruleList = 
		List.Tot.collect
			(fun elem ->
				match elem.rule with
				| PSeq(e, a, l) -> epsInRule e ruleList
				| PRef(t, _) -> isEps t.text ruleList
				| _ -> []
			) elements *)
	
	val newBodyCreateElem: elem 'a 'b -> int -> list (Rule 'a  'b) -> Tot (list (elem 'a 'b))
	let newBodyCreateElem elem i ruleList =
		match elem.rule with
		| PRef(t, _) ->
			if not (List.Tot.isEmpty (isEps t.text ruleList))
			then [TransformAux.createSimpleElem (PRef(new_Source0(string_of_int i), None)) elem.binding]
			else [elem]	
		| _ -> [elem]
		
	val newBody: list (elem 'a 'b) -> int -> list (Rule 'a  'b) -> Tot (list (elem 'a 'b))
	let rec newBody elements i ruleList =
		match elements with 
		| [] -> []
		| hd::tl -> List.Tot.append (newBodyCreateElem hd i ruleList) (newBody tl (i + 1) ruleList)			
	
	val nth: list 'a -> int -> Tot (option 'a)
	let rec nth l n = match l with
	  | []     -> None
	  | hd::tl -> if n = 0 then Some hd 
				  else if n < 0 then None else nth tl (n - 1)
  
	val addRule: Rule 'a  'b -> list string  -> list int -> Tot (list (Rule 'a  'b))
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
							(* WARNING: 'if' cannot be used in patterns *)
							(match (nth epsRef (snd (int32_tryParse t.text) - 1))  with 
							| Some x -> [TransformAux.createSimpleElem (PRef(new_Source0(x), None)) elem.binding]
							| None -> [])
						else [elem]																													
				| _ -> [elem]
			) (match numberRule.body with PSeq(e, a, l) -> e | _ -> []) in 
			
		let ac,lbl = match numberRule.body with PSeq(e, a, l) -> a,l | _ -> None,None in			
		[{numberRule with body=PSeq(newBody, ac, lbl)}]

				
	//-- Функция для добавления нового правила
	val newRule: Rule 'a  'b -> list string -> list (Rule 'a  'b) -> Tot (list (Rule 'a  'b))
	let newRule rule epsRef ruleList =
		if not (List.Tot.isEmpty epsRef) then
			let numberEpsRef = genSubsets (List.Tot.length epsRef) in
			
			let ac, lbl = match rule.body with PSeq(e, a, l) -> a,l | x -> None,None in			

			let numberBody =
				match rule.body with
				|PSeq(elements, _, _) -> 
					PSeq(newBody elements 0 ruleList, ac, lbl)
				|_ -> rule.body in			
			
			let numberRule = {rule with body=numberBody} in
				List.Tot.collect (addRule numberRule epsRef) numberEpsRef
		else [] 
		
	//удаление правил вида A -> A
	val trashFilter: Rule 'a  'b -> Tot bool
	let trashFilter rule =  
		let elements = match rule.body with PSeq(e, _, _) -> e | _ -> [] in
			if List.Tot.length elements = 1 then 
				match (List.Tot.hd elements).rule with
				| PRef (e,_) -> not (rule.name.text = e.text)
				| _ -> true
			else true
		
	val deleteTrashRule: list (Rule 'a  'b) -> Tot (list (Rule 'a  'b))
	let deleteTrashRule rulesList = 
		List.Tot.filter(fun rule -> trashFilter rule) rulesList
	
	val newRules: list (Rule 'a  'b) -> Tot (list (Rule 'a  'b))
	let newRules ruleList = 
		// --Добавляем новые правила     
		List.Tot.collect
				(fun rule ->
					match rule.body with
					| PSeq(elements, actionCode, lbl) ->
						if not (List.Tot.isEmpty elements) 
						then List.Tot.append (newRule rule (epsInRule elements ruleList) ruleList) [rule]
						else []	                
					| _ -> []
				) ruleList

	//TODO: доказать progress: в результате нет eps-правил
	val deleteEpsRule: list (Rule 'a  'b) -> Tot (list (Rule 'a  'b))
    let deleteEpsRule (ruleList: list (Rule _ _)) =                  
        let rulesFilter =  List.Tot.filter (fun r -> not (match r.body with PSeq([],_,_) -> true | _ -> false)) (newRules ruleList) in 
			deleteTrashRule rulesFilter