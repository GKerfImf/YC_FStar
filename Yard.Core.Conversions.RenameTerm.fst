module Yard.Core.Conversions.RenameTerm
    open IL
    open Yard.Core.Conversions

//--Переименование терминалов в нетерминалы в неподходящих правилах (вида s -> AB, s -> Ab, s -> bA)-------------------

    val isToken: elem 'a 'b -> Tot bool
    let isToken elem = match elem.rule with PToken _ -> true | _ -> false

    val isRef: elem 'a 'b -> Tot bool
    let isRef elem = match elem.rule with PRef(_,_) -> true | _ -> false


    let renameTerm ruleList = 
        let isCNF (rule: Rule _ _) = 
            match rule.body with
            | PSeq(elements,_,_) 
                (* when (elements |> List.length = 1) *) -> true 
            | PSeq(elements,_,_) 
                (* when (elements |> List.length = 2 && isRef (List.nth elements 0) && isRef (List.nth elements 1)) *) -> true 
            | PSeq([],_, _) 
                (* when rule.isStart *) -> true 
            | _ -> false in
        []

        (*
        let newRuleList = ref [] in

        let renameRule (rule: Rule _ _) = 

            let rename (elem: elem _ _) = 
                if isToken elem then 
                    let newRuleName = new_Source0("new_" ^ (match elem.rule with PToken t -> t.text | _ -> "")) in 
                    if (not (!newRuleList |> List.existsb (fun rl -> rl.name = newRuleName))) then
                        let newRule = TransformAux.createRule newRuleName rule.args (PSeq([elem], None, None)) false rule.metaArgs in 
                        newRuleList := !newRuleList @ [newRule];
                    TransformAux.createSimpleElem (PRef(newRuleName, None)) elem.binding
                else 
                    elem in

            let elements = match rule.body with PSeq(e, a, l) -> e | x -> [] in
            let elems = [rename (List.nth elements 0); rename (List.nth elements 1)] in
            [{rule with body =
                (match rule.body with
                | PSeq(e, a, l) -> elems, a, l
                | _ -> elems, None, None)
                    |> PSeq }] in
        
        in
        (ruleList |> List.collect (fun rule -> if isCNF rule then [rule] else renameRule rule)) @ !newRuleList
        *)
