module Yard.Core.Conversions.RenameTerm
    open IL
    open Yard.Core.Conversions

//--Переименование терминалов в нетерминалы в неподходящих правилах (вида s -> AB, s -> Ab, s -> bA)-------------------

    val isToken: elem 'a 'b -> Tot bool
    let isToken elem = match elem.rule with PToken _ -> true | _ -> false

    val isRef: elem 'a 'b -> Tot bool
    let isRef elem = match elem.rule with PRef(_,_) -> true | _ -> false
	
    val isCNF: Rule 'a 'b -> Tot bool
    let isCNF rule =
        match rule.body with
        | PSeq(elements,_,_) -> (List.Tot.length elements = 1) || 
								(List.Tot.length elements = 2 && isRef (List.Tot.hd elements) && isRef (List.Tot.hd (List.Tot.tl elements))) ||
								(List.Tot.length elements = 0 && rule.isStart)	
        | _ -> false   
		
	val lengthBodyRule: Rule 'a 'b -> Tot int
    let lengthBodyRule rule = List.length (match rule.body with PSeq(e, a, l) -> e | _ -> [])
	
	val renameRule: rule : (Rule 'a 'b){lengthBodyRule rule = 2} -> list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
	let renameRule rule newRuleList = 		
		let rename elem = 
			if isToken elem then 
				let newRuleName = new_Source0("new_" ^ (match elem.rule with PToken t -> t.text | _ -> "")) in 
			
				if (not (List.Tot.existsb (fun rl -> rl.name = newRuleName) newRuleList)) then
					let newRule = TransformAux.createRule newRuleName rule.args (PSeq([elem], None, None)) false rule.metaArgs in 
					(TransformAux.createSimpleElem (PRef(newRuleName, None)) elem.binding, [newRule])
				else (TransformAux.createSimpleElem (PRef(newRuleName, None)) elem.binding, [])
			else (elem, []) in 
		
		let elements = match rule.body with PSeq(e, _, _) -> e | x -> [] in
		
		let elem0 = rename (List.Tot.hd elements) in
		let elem1 = rename (List.Tot.hd (List.Tot.tl elements)) in 
		let elems = [fst elem0; fst elem1] in
			
		let renameElem = 
			[{rule with body =
			(match rule.body with
			| PSeq(e, a, l) -> PSeq(elems, a, l)
			| _ -> PSeq(elems, None, None) )}] in  
		let newRuleEls =  List.Tot.append (snd elem0) (snd elem1) in 
			List.Tot.append renameElem newRuleEls
	
	val renameTerm_acc: list (Rule 'a 'b) -> list (Rule 'a 'b) -> 
						(Rule 'a 'b -> list (Rule 'a 'b) -> Tot (list (Rule 'a 'b)))
						-> Tot (list (Rule 'a 'b)) 
	let rec renameTerm_acc ruleList acc f =
		match ruleList with 
		| [] -> acc
		| hd::tl -> renameTerm_acc tl (List.Tot.append acc (f hd acc)) f

	assume val renameTerm: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
	(* let renameTerm ruleList = renameTerm_acc ruleList [] (fun rule acc -> if isCNF rule then [rule] else renameRule rule acc) *)