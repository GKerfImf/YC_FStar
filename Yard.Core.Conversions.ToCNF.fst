module Yard.Core.Conversions.ToCNF
	open IL
	open Yard.Core //.Namer


//--Разделение длинных правил на правила длины 2 и 1 ------------------------------------------------------------------------

	let splitLongRule rules =    

	    let newRuleList = ref [] in

	    let rec cutRule (rule: Rule _ _) = 

	        let elements = match rule.body with PSeq(e, a, l) -> e | _ -> [] in

	        if List.length elements > 2 then
	            let revEls = elements |> List.rev in
	            let ruleBody = PSeq([revEls |> List.hd; revEls |> List.tl |> List.hd], None, None) in
	            let newRule = TransformAux.createRule (Namer.newSource(rule.name)) rule.args ruleBody false rule.metaArgs in     
	            let newElem = TransformAux.createDefaultElem (PRef(newRule.name, None)) in
	            let changedRule = (revEls |> List.tl |> List.tl |> List.rev) @ [newElem] in

				//newRuleList := !newRuleList @ [newRule]

                cutRule ({ rule with body = 
	            				PSeq(
	            					changedRule, 
	            					(match rule.body with PSeq(e, a, l) -> a | _ -> None),
	            					(match rule.body with PSeq(e, a, l) -> l | _ -> None)) })

	        else [rule]
	    in
	    (rules |> List.collect (fun rule -> cutRule rule)) @ !newRuleList


	let deleteTrashRule rulesList = 
    	let trashFilter rule =  
    		let elements = match rule.body with PSeq(e, _, _) -> e | _ -> [] in
        		if List.length elements = 1 then 
                	match (List.hd elements).rule with
                	| PRef (e,_) -> rule.name.text = e.text |> not  //rule.name.text.Equals(e.text) |> not
                	| _ -> true
            	else true
        in
		rulesList |> List.filter(fun rule -> trashFilter rule)


//Код ниже ещё не должен работать
//--Функция для удаления эпсилон-правил------------------------------------------------------------

let deleteEpsRule (ruleList: list (Rule _ _)) =
    let rec pown a n = 
        match n with 
        | 0 -> 1
        | _ -> a * (pown a (n-1)) in
    let rec listfromto a b =
        match b-a+1 with
        | 0 -> []
        | _ -> (listfromto a (b-1)) @[b] in
	let rec powerset = 
  		function
  		| [] -> [[]]
  		| x::xs -> List.collect (fun subset -> [subset; x::subset]) (powerset xs) in

  	//Powerset [1..N]
    let genSubsets n = listfromto 1 n |> powerset in

    // Список всех правил
    //"When clauses are not yet supported in --verify mode; they soon will be"
    let epsList = 
        ruleList |> List.collect
            (fun rule -> 
                match rule.body with
                | PSeq(elements, actionCode, lbl) -> 
                	if List.isEmpty elements then [rule.name.text] else []
                | _ -> []
            ) in

    // Проверка вхождения эпсилон-правила
    let isEps s = epsList |> List.filter (fun x -> x = s) in


    //Список эпсилон-правил входящих в данное правило  
    let rec epsInRule elements = 
            elements |> List.collect
                        (fun elem ->
                            match elem.rule with
                            | PSeq(e, a, l) -> epsInRule e
                            | PRef(t, _) -> isEps t.text
                            | _ -> []
                        ) in
    

    //Функция для добавления нового правила
    let newRule (rule: Rule _ _) (epsRef: list _) =         
        if epsRef |> List.isEmpty |> not then
            let numberEpsRef = genSubsets List.length epsRef in
            let ac, lbl = match rule.body with PSeq(e, a, l) -> a,l | x -> None,None in
            let i = ref 0 in
            let newBody elements =
                elements 
                |> List.collect
                    (fun elem ->
                        match elem.rule with
                        | PRef(t, _) when (t.text |> isEps |> List.isEmpty |> not) ->
                                    incr i
                                    [TransformAux.createSimpleElem (PRef(Source.t(string !i), None)) elem.binding]
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
                    |> List.map string
                    |> List.existsb (fun x -> x = t)
                    in
                let ac,lbl = match numberRule.body with PSeq(e, a, l) -> a,l | _ -> None,None in
                let newBody = 
                    match numberRule.body with PSeq(e, a, l) -> e | _ -> []
                    |> List.collect
                        (fun elem ->
                            match elem.rule with
                            | PRef(t,_) when epsWithNameExists t.text -> []
                            | PRef(t,_) when System.Int32.TryParse t.text |> fst && not <| epsWithNameExists t.text -> 
                                      [TransformAux.createSimpleElem (PRef(Source.t(epsRef.[int t.text - 1]), None)) elem.binding]
                            | _ -> [elem])
                [{numberRule with body=PSeq(newBody, ac, lbl)}]
            let numberRule = {rule with body=numberBody}
            numberEpsRef |> List.collect (addRule numberRule)
        else []     
            
    //Добавляем новые правила
    ruleList |> List.collect
        (fun rule ->
            match rule.body with
            | PSeq(elements, actionCode, lbl) when not elements.IsEmpty ->
                newRule rule (epsInRule elements) @ [rule]
            | _ -> []
        )
    |> List.filter (fun r -> not <| match r.body with PSeq([],_,_) -> true | _ -> false) |> deleteTrashRule








