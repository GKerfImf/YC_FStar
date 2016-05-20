module Yard.Core.Conversions.SplitLongRule
    open IL
    open Yard.Core
    open Yard.Core.Conversions
    open FStar.ListProperties

    val rev_length : l:(list 'a)-> 
        Lemma 
            (requires True) 
            (ensures (List.length (List.rev l) = List.length l)) 
            [SMTPat (List.rev l)]
    let rev_length l = rev_acc_length l []

    val tail_length : l:(list 'a){is_Cons l}  -> 
        Lemma 
            (requires True)
            (ensures (List.length (List.Tot.tl l) = (List.length l) - 1)) 
            [SMTPat (List.Tot.tl l)]
    let tail_length l = ()
	
	val append_ShortRulesL: 
		rule1:(list (Rule 'a  'b)) {List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) rule1} 
        -> rule2:(list (Rule 'a  'b)) {List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) rule2} 
        -> Lemma 
            (requires true) 
            (ensures (List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) (List.Tot.append rule1 rule2))) 
            [SMTPat (List.Tot.append rule1 rule2)]		
	let rec append_ShortRulesL rule1 rule2 = match rule1 with
	  | [] -> ()
	  | hd::tl -> append_ShortRulesL tl rule2	
	
    val getShortPSeq:
        listRev:(list (elem 'a 'b)){List.length listRev > 2}
        -> Tot (body:(Production 'a 'b){ (fun body -> (List.length (match body with PSeq(e, a, l) -> e | _ -> []) <= 2 )) body})
    let getShortPSeq revEls = PSeq([List.Tot.hd revEls; List.Tot.hd (List.Tot.tl revEls)], None, None)

    val getListOfShort:
        acc:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) acc} 
        -> item:(Rule 'a  'b){TransformAux.lengthBodyRule item <= 2}
        -> Tot (result:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) result} )
    let getListOfShort acc item = List.Tot.append acc [item]
		
	//Не выводит правильные типы, когда вместо getListOfShort используется List.Tot.append
    val cutRule: 
        rule : (Rule 'a 'b) 
        -> resultRuleList:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) resultRuleList} 
        -> Tot (result:(list (Rule 'a 'b)){List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) result} ) (decreases %[ TransformAux.lengthBodyRule rule; List.length resultRuleList])
    let rec cutRule rule resultRuleList = 
        let elements = match rule.body with PSeq(e, a, l) -> e | _ -> [] in
        if List.length elements > 2 then
            let revEls = List.rev elements in 
            let ruleBody = getShortPSeq revEls in
            let newRule = TransformAux.createRule (Namer.newSource (List.length resultRuleList) rule.name) rule.args ruleBody false rule.metaArgs in 
            let newElem = TransformAux.createDefaultElem (PRef(newRule.name, None)) in
            let changedRule = List.rev (List.Tot.tl (List.Tot.tl revEls)) @ [newElem] in

            cutRule ({ rule with body = 
                            PSeq(
                                changedRule, 
                                (match rule.body with PSeq(e, a, l) -> a | _ -> None),
                                (match rule.body with PSeq(e, a, l) -> l | _ -> None)) }) (getListOfShort resultRuleList newRule)
                    
        else
            getListOfShort resultRuleList ({ rule with name = Namer.newSource (List.length resultRuleList) rule.name})  		  	  
		
	val append_ShortRules: 
		rule1:(list (Rule 'a  'b)) {List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) rule1} 
        -> rule2:(list (Rule 'a  'b)) {List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) rule2} 
        -> Tot (result:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) result})
	let rec append_ShortRules rule1 rule2 = match rule1 with
	  | [] -> rule2
	  | hd::tl -> hd::append_ShortRules tl rule2
  
	val collect_ShortRules: 
		((Rule 'a  'b) -> Tot (l:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) l} ))
		-> list (Rule 'a  'b) 		
		-> Tot (result:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) result})
	let rec collect_ShortRules f l = match l with
		| [] -> []
		| hd::tl -> append_ShortRules (f hd) (collect_ShortRules f tl)
	
	//Не понятно, почему F* сам не может вывести тип для List.Tot.collect, когда есть лемма для List.Tot.append	(append_ShortRulesL)	
    val splitLongRule: 
		ruleList : list (Rule 'a 'b) 
	    -> Tot (result:(list (Rule 'a 'b)){List.Tot.for_all (fun x -> TransformAux.lengthBodyRule x <= 2) result})
    let splitLongRule ruleList = collect_ShortRules (fun rule -> cutRule rule []) ruleList		