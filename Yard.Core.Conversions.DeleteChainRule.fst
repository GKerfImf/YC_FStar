module Yard.Core.Conversions.DeleteChainRule
    open IL

//--Функция для удаления цепных правил-------------------------------------------------------------------------------------------- 

    val label: Rule 'a 'b -> Tot (option DLabel)
    let label (rl: Rule _ _) = 
        match rl.body with 
        |PSeq(_, _, l) -> l 
        | _ -> None

    val bodyChange: Rule 'a 'b -> Rule 'a 'b -> Tot (Production 'a 'b)
    let bodyChange (mR: Rule _ _) (r: Rule _ _) =
        match label mR with
        | Some x -> 
            PSeq(match r.body with PSeq(e, a, _) -> e, a, Some x | _ -> [], None, Some x)
        | _ -> r.body

    val isOneRule: Rule 'a 'b -> Tot bool 
    let isOneRule rule =
        match rule.body with
        | PSeq(elements, actionCode, lbl) -> 
            (List.length elements = 1) && (match (List.Tot.hd elements).rule with PRef(t,_) -> true | _ -> false)
        | _ -> false
	//TODO: доказать тотальность
    val newRule: list (Rule 'a 'b) -> Rule 'a 'b -> string -> (list (Rule 'a 'b))
    let rec newRule (ruleList: list (Rule _ _)) (mainRule: Rule _ _) (name:string) =
        List.collect
            (fun rule ->
                if rule.name.text = name then
                    if isOneRule rule then
                        match rule.body with
                        | PSeq(elements, actionCode, lbl) -> 
                            newRule ruleList mainRule (match (List.hd elements).rule with PRef(t, _) -> t.text | _ -> "")
                        | _ -> newRule ruleList mainRule ""
                    else
                        [{mainRule with body = bodyChange mainRule rule}] 
                else []
            )
            ruleList
	//TODO: доказать тотальность и progress: в результате нет цепных правил
    val deleteChainRule: ruleList: list (Rule 'a 'b) -> (list (Rule 'a 'b))
    let deleteChainRule (ruleList: list (Rule _ _)) = 
        List.collect
            (fun rule -> 
                match rule.body with
                | PSeq(elements, actionCode, lbl) ->
                    (match ((List.length elements) = 1 && (match (List.hd elements).rule with PRef(_, _) -> true | _ -> false)) with 
                        | true -> newRule ruleList rule (match (List.hd elements).rule with PRef(t, _) -> t.text | _ -> "")
                        | _ -> [rule])
                | _ -> [rule]) 
            ruleList