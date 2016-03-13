module Yard.Core.Conversions.ToCNF
    open IL
    open Yard.Core.Conversions

    // TODO -- Как сильно можно менять код?
    // TODO -- Как лучше заменять when?
    // TODO -- Rule 'patt 'expr ~> Rule 'a 'b 

(*
//--Разделение длинных правил на правила длины 2 и 1 ------------------------------------------------------------------------

    val splitLongRule: ruleList: list (Rule 'a 'b) -> list (Rule 'a 'b)
    let splitLongRule (ruleList: list (Rule _ _)) =    
        let newRuleList = ref [] in
        let rec cutRule (rule: Rule _ _) = 

            // TODO: -- Написать тут тип не получится?
            //--val elements: (Rule 'a 'b) -> Tot (list (elem 'a 'b))
            let elements = match rule.body with PSeq(e, a, l) -> e | _ -> [] in

            if List.length elements > 2 then
                let revEls = elements |> List.rev in
                let ruleBody = PSeq([revEls |> List.hd; revEls |> List.tl |> List.hd], None, None) in

                // TODO: -- Namer.newSource ~(?)~> Tot   см. ниже
                // TODO: -- Namer.newSource(Source) ~~> Namer.newSource(Rule or ListRule)
                let newRule = TransformAux.createRule (Namer.newSource(rule.name)) rule.args ruleBody false rule.metaArgs in 
 
                let newElem = TransformAux.createDefaultElem (PRef(newRule.name, None)) in

                let changedRule = (revEls |> List.tl |> List.tl |> List.rev) @ [newElem] in

                newRuleList := !newRuleList @ [newRule];
 
                cutRule ({ rule with body = 
                                PSeq(
                                    changedRule, 
                                    (match rule.body with PSeq(e, a, l) -> a | _ -> None),
                                    (match rule.body with PSeq(e, a, l) -> l | _ -> None)) })
            else 
                [rule]
        in
        (ruleList |> List.collect (fun rule -> cutRule rule)) @ !newRuleList



    val length_body: Rule 'a 'b -> Tot nat
    let length_body rule =
        match rule.body with 
        |PSeq(e, a, l) -> List.length e 
        | _ -> 0 //1?

    assume val short_right_rules_lemma : 
        r: list (Rule 'a 'b) ->
            Lemma 
                (ensures 
                    List.Tot.for_all (fun x -> x<=2) (List.Tot.map length_body (r)) 
                    //--  				+
                    //--	     splitLongRule is Tot
                    //--                =
                    //--for_all (fun x -> x<=2) (map length_body (splitLongRule r)) 
                )
*)
(*
// -- Функция для удаления эпсилон-правил-----------------------------------------------------------
    //TODO: --Что делать с реализацией?
    assume val int32_tryParse : string -> Tot (bool * int)

    let deleteEpsRule (ruleList: list (Rule _ _)) =
        let rec listfromto a b =
            match b-a+1 with
            | 0 -> []
            | _ -> (listfromto a (b-1)) @[b] in
        let rec powerset = 
            function
            | [] -> [[]]
            | x::xs -> List.collect (fun subset -> [subset; x::subset]) (powerset xs) in

        //--Powerset [1..N]
        let genSubsets n = listfromto 1 n |> powerset in

        // Список всех правил
        let epsList = 
            ruleList |> List.collect
                (fun rule -> 
                    match rule.body with
                    | PSeq(elements, actionCode, lbl) -> 
                        if List.isEmpty elements then [rule.name.text] else []
                    | _ -> []
                ) in

        //-- Проверка вхождения эпсилон-правила
        let isEps s = epsList |> List.filter (fun x -> x = s) in


        //-- Список эпсилон-правил входящих в данное правило  
        let rec epsInRule elements = 
                elements |> List.collect
                            (fun elem ->
                                match elem.rule with
                                | PSeq(e, a, l) -> epsInRule e
                                | PRef(t, _) -> isEps t.text
                                | _ -> []
                            ) in

        //-- Функция для добавления нового правила
        let newRule (rule: Rule _ _) (epsRef: list _) =         
            if not (epsRef |> List.isEmpty) then
                let numberEpsRef = epsRef |> List.length |> genSubsets in
                let ac, lbl = match rule.body with PSeq(e, a, l) -> a,l | x -> None,None in
                let i = ref 0 in
                let newBody elements =
                    elements 
                    |> List.collect
                        (fun elem ->
                            match elem.rule with
                            | PRef(t, _) 
                                (* when t.text |> isEps |> List.isEmpty |> not *) ->
                                    i := !i + 1;
                                    [TransformAux.createSimpleElem (PRef(new_Source0(string_of_int !i), None)) elem.binding]
                            | _ -> [elem]
                        ) in

                let numberBody =
                    match rule.body with
                    |PSeq(elements, _, _) -> 
                        PSeq(newBody elements, ac, lbl)
                    |_ -> rule.body in

                let rulename = rule.name in

                let addRule (numberRule: Rule _ _) eps =
                    let epsWithNameExists t = 
                        eps
                        |> List.map string_of_int
                        |> List.existsb (fun x -> x = t)
                        in
                    let ac,lbl = match numberRule.body with PSeq(e, a, l) -> a,l | _ -> None,None in
                    let newBody = 
                        match numberRule.body with PSeq(e, a, l) -> e | _ -> []
                        |> List.collect
                            (fun elem ->
                                match elem.rule with
                                | PRef(t,_) 
                                    (* when epsWithNameExists t.text *) -> []
                                | PRef(t,_)
                                    //TODO: --System.Int32.TryParse ~~> assume int32_tryParse
                                    (* when int32_tryParse t.text |> fst && not <| epsWithNameExists t.text) *) -> [] 
                                    (* [TransformAux.createSimpleElem (PRef(new_Source0(epsRef.[(int Source.text) - 1]), None)) elem.binding] *)
                                | _ -> [elem]
                            )  in
                    [{numberRule with body=PSeq(newBody, ac, lbl)}] in

                let numberRule = {rule with body=numberBody} in
                numberEpsRef |> List.collect (addRule numberRule) 
            else [] 
        in

        let deleteTrashRule rulesList = 
            let trashFilter rule =  
                let elements = match rule.body with PSeq(e, _, _) -> e | _ -> [] in
                    if List.length elements = 1 then 
                        match (List.hd elements).rule with
                        | PRef (e,_) -> rule.name.text = e.text |> not
                        | _ -> true
                    else true in
            rulesList |> List.filter(fun rule -> trashFilter rule) in

        // --Добавляем новые правила
        ruleList |> List.collect
            (fun rule ->
                match rule.body with
                //| PSeq(elements, actionCode, lbl) when (elements |> List.isEmpty |> not) -> newRule rule (epsInRule elements) @ [rule]
                | PSeq(elements, actionCode, lbl) -> newRule rule (epsInRule elements) @ [rule]
                | _ -> []
            )
        |> List.filter (fun r -> match r.body with PSeq([],_,_) -> true | _ -> false |> not) |> deleteTrashRule
*)
(*
//--Функция для удаления цепных правил-------------------------------------------------------------------------------------------- 
    
    val deleteChainRule: ruleList: list (Rule 'a 'b) -> list (Rule 'a 'b)
    let deleteChainRule (ruleList: list (Rule _ _)) = 
        let rec newRule (mainRule: Rule _ _) name =
            ruleList |> List.collect
                (fun rule ->
                    let isOneRule rule =
                        match rule.body with
                        | PSeq(elements, actionCode, lbl) -> 
                            (((List.length elements) = 1) && (match (List.hd elements).rule with PRef(t,_) -> true | _ -> false))
                        | _ -> false in

                    let label (rl: Rule _ _) = match rl.body with PSeq(_, _, l) -> l | _ -> None in

                    let bodyChange (mR: Rule _ _) (r: Rule _ _) =
                        match label mR with
                        | Some x -> 
                            PSeq(match r.body with PSeq(e, a, _) -> e, a, Some x | _ -> [], None, Some x)
                        | _ -> r.body
                    in

                    if rule.name.text = name then
                        if isOneRule rule then
                            match rule.body with
                            | PSeq(elements, actionCode, lbl) -> 
                                newRule mainRule (match (List.hd elements).rule with PRef(t, _) -> t.text | _ -> "")
                            | _ -> (newRule mainRule "")
                        else
                            [{mainRule with body = bodyChange mainRule rule}] 
                    else []
                )
        in
        ruleList |> List.collect
            (fun rule -> 
                match rule.body with
                | PSeq(elements, actionCode, lbl) ->
                    (match ((List.length elements) = 1 && (match (List.hd elements).rule with PRef(_, _) -> true | _ -> false)) with 
                        | true -> newRule rule (match (List.hd elements).rule with PRef(t, _) -> t.text | _ -> "")
                        | _ -> [rule])
                | _ -> [rule]
            )
*)
(*
//--Переименование терминалов в нетерминалы в неподходящих правилах (вида s -> AB, s -> Ab, s -> bA)-------------------
    let renameTerm ruleList = 
        let isToken (elem: elem _ _) = match elem.rule with PToken _ -> true | _ -> false in
        let isRef (elem: elem _ _) = match elem.rule with PRef(_,_) -> true | _ -> false in 
        let isCNF (rule: Rule _ _) = 
            match rule.body with
            | PSeq(elements,_,_) 
                (* when (elements |> List.length = 1) *) -> true 
            | PSeq(elements,_,_) 
                (* when (elements |> List.length = 2 && isRef (List.nth elements 0) && isRef (List.nth elements 1)) *) -> true 
            | PSeq([],_, _) 
                (* when rule.isStart *) -> true 
            | _ -> false in


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
    
//--CNF--------------------------------------------------------------------------------------------------------
    let toCNFrule (ruleList: list (Rule _ _)) = 
        ruleList
        |> SplitLongRule.splitLongRule
        |> DeleteEpsRule.deleteEpsRule 
        |> DeleteChainRule.deleteChainRule
        |> RenameTerm.renameTerm 


//-- Main lemma sketch

assume val grammar_eq : g1:Grammar 'a 'b -> g2:Grammar 'a 'b -> Tot bool

assume val isCFG:  g:Grammar 'a 'b -> Tot bool
assume val isCNF:  g:Grammar 'a 'b -> Tot bool
assume val toCNF:  g:Grammar 'a 'b -> Tot (Grammar 'a 'b)

assume val main_lemma: 
	g: Grammar 'a 'b -> 
		Lemma 
			(requires (isCFG g)) 
			(ensures ( isCNF (toCNF g) /\ grammar_eq (toCNF g) (g) ))
