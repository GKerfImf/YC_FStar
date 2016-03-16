module Yard.Core.Conversions.RenameTerm
    open IL
    open Yard.Core.Conversions


//--Переименование терминалов в нетерминалы в неподходящих правилах (вида s -> AB, s -> Ab, s -> bA)-------------------

// infix operator? :(

    val isToken: elem 'a 'b -> Tot bool
    let isToken elem = match elem.rule with PToken _ -> true | _ -> false

    val isRef: elem 'a 'b -> Tot bool
    let isRef elem = match elem.rule with PRef(_,_) -> true | _ -> false

    val isRefOpt: option (elem 'a 'b) -> Tot bool
    let isRefOpt elemopt =
        match elemopt with
        | Some elem -> isRef elem
        | None -> false


//assume val instanceOf: a:Type -> Tot a
 
    assume val toTerminalRule: 
        x:(Rule 'a 'b){
            (fun x ->  
                match x.body with
                | PSeq(elements,_,_) -> List.length elements = 1 && isToken (List.Tot.hd elements) 
                | _ -> false) 
            x 
        }
    assume val toTwoNonTermRule: 
        x:(Rule 'a 'b){
            (fun x ->  
                match x.body with
                | PSeq(elements,_,_) -> List.length elements = 2 && isRefOpt (List.Tot.nth elements 0) && isRefOpt (List.Tot.nth elements 1)
                | _ -> false) 
            x 
        }
    assume val startRule: x:(Rule 'a 'b){ (fun x -> match x.body with PSeq([],_,_) -> x.isStart | _ -> false) x }

    val isCNF: Rule 'a 'b -> Tot bool
    let isCNF (rule: Rule 'a 'b) = 
        match rule with 
        | toTerminalRule -> true
        | toTwoNonTermRule -> true
        | startRule -> true 
        | _ -> false
    
    let renameTerm ruleList = 

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
