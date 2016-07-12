module Yard.Core.Conversions.RenameTerm
    open IL

    val isSingle: Rule 'a 'b -> Tot bool
	let isSingle rule =   
	    match rule.body with
	    | PSeq(elems,_,_) -> List.Tot.length elems = 1 && Helpers.isPToken (List.Tot.hd elems).rule 
	    | _ -> false

	val renameRule: Rule 'a 'b -> Tot (list (Rule 'a 'b))
	let renameRule rule =

	    let renameElem elem rule = 
	        if Helpers.isPToken elem.rule then 
	            let newRuleName = new_Source0("New_" ^ (match elem.rule with | PToken t -> t.text | _ -> "")) in
	            let newRule = TransformAux.createRule newRuleName rule.args (PSeq([elem], None, None)) false rule.metaArgs in
	            (TransformAux.createSimpleElem (PRef(newRuleName, None)) elem.binding , [newRule])
	        else (elem, []) in

	    let res = match rule.body with PSeq(elems,_,_) -> List.Tot.map (fun elem -> renameElem elem rule) elems | _ -> [] in 
	    
	    let newBody = 
	    	match rule.body with 
	    	| PSeq(el,a,l) -> PSeq(List.Tot.map fst res, a, l) 
	    	| _ -> PSeq([], None, None) in

	    List.Tot.append [{rule with body = newBody}] (List.Tot.fold_left (fun x y -> List.Tot.append x y) ([]) (List.Tot.map snd res))
	
	val renameTerm: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
	let renameTerm ruleList = 
		Helpers.removeDuplicates (
			List.Tot.fold_left (fun x y -> List.Tot.append x y) ([]) (
				List.Tot.map (fun rule -> if isSingle rule then [rule] else renameRule rule) (
					ruleList)))