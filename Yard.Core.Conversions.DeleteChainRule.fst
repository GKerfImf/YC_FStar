module Yard.Core.Conversions.DeleteChainRule
    open IL

//--Функция для удаления цепных правил-------------------------------------------------------------------------------------------- 

    val label: Rule 'a 'b -> Tot (option DLabel)
    let label rl = 
        match rl.body with 
        |PSeq(_, _, l) -> l 
        | _ -> None

    val bodyChange: Rule 'a 'b -> Rule 'a 'b -> Tot (Production 'a 'b)
    let bodyChange mR r =
        match label mR with
        | Some x -> 
            PSeq(match r.body with PSeq(e, a, _) -> e, a, Some x | _ -> [], None, Some x)
        | None -> r.body

    val isOneRule: Rule 'a 'b -> Tot bool 
    let isOneRule rule =
        match rule.body with
        | PSeq(elements, _, _) -> 
            (List.length elements = 1) && (match (List.Tot.hd elements).rule with PRef(t,_) -> true | _ -> false)
        | _ -> false
	
	//lengthRL -- количество правил уменьшается, когда удаляются цепные правила
    val newRule: list (Rule 'a 'b) -> Rule 'a 'b -> lengthRL : nat -> string -> Tot (list (Rule 'a 'b)) (decreases %[lengthRL])
    let rec newRule ruleList mainRule lengthRL name =
        List.Tot.collect
            (fun rule ->
                if (rule.name.text = name) && (lengthRL > 0) then
					if isOneRule rule then
                        match rule.body with
                        | PSeq(elements, _, _) -> 
							let elem0 = List.Tot.hd elements in 
								newRule ruleList mainRule (lengthRL - 1) (match elem0.rule with PRef(t, _) -> t.text | _ -> "")
                        | _ -> newRule ruleList mainRule (lengthRL - 1) ""
                    else
                        [{mainRule with body = bodyChange mainRule rule}] 
                else []
			) ruleList 
			
	//TODO: доказать progress: в результате нет цепных правил
    val deleteChainRule: ruleList: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
    let deleteChainRule ruleList = 
		let lengthRuleList = List.length ruleList in 
        List.Tot.collect
            (fun rule -> 
                match rule.body with
                | PSeq(elements, actionCode, lbl) ->					
                    (match ((List.length elements) = 1 && (let elem0 = List.Tot.hd elements in match elem0.rule with PRef(_, _) -> true | _ -> false)) with 
                        | true -> newRule ruleList rule lengthRuleList (let elem0 = List.Tot.hd elements in match elem0.rule with PRef(t, _) -> t.text | _ -> "")
                        | _ -> [rule])
                | _ -> [rule]
			) ruleList