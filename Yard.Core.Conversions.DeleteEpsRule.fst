module Yard.Core.Conversions.DeleteEpsRule
    open IL
    open Yard.Core.Conversions

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
