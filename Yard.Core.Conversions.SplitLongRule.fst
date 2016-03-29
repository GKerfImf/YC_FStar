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


    
    val lengthBodyRule: Rule 'a 'b -> Tot int
    let lengthBodyRule rule = List.length (match rule.body with PSeq(e, a, l) -> e | _ -> [])

    val getShortPSeq:
        listRev:(list (elem 'a 'b)){List.length listRev > 2}
        -> Tot (body:(Production 'a 'b){ (fun body -> (List.length (match body with PSeq(e, a, l) -> e | _ -> []) <= 2 )) body})
    let getShortPSeq revEls = PSeq([List.Tot.hd revEls; List.Tot.hd (List.Tot.tl revEls)], None, None) 


    val cutRule: 
        rule : (Rule 'a 'b) 
        -> resultRuleList:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> lengthBodyRule x <= 2) resultRuleList} 
        -> Tot (list (Rule 'a 'b)) (decreases %[ lengthBodyRule rule; List.length resultRuleList])
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
                                (match rule.body with PSeq(e, a, l) -> l | _ -> None)) }) ([]) //resultRuleList @ [newRule]
                    
        else
            resultRuleList @ [{ rule with name = Namer.newSource (List.length resultRuleList) rule.name}]


    val splitLongRule: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
    let splitLongRule ruleList = List.Tot.collect (fun rule -> cutRule rule []) ruleList

(*
    val mon_inc_cutRule_lemma: rule: (Rule 'a 'b) -> resultRuleList: list (Rule 'a 'b) ->
        Lemma
            (requires ( True )) 
            (ensures ( List.length (cutRule rule resultRuleList) > List.length resultRuleList ))
            (decreases %[ lengthBodyRule rule; List.length resultRuleList])
            [SMTPat ( cutRule rule resultRuleList )]
    let rec mon_inc_cutRule_lemma rule resultRuleList =
        let elements = match rule.body with PSeq(e, a, l) -> e | _ -> [] in
        if lengthBodyRule rule > 2 
        then
            let revEls = List.rev elements in 
            let ruleBody = PSeq([List.Tot.hd revEls; List.Tot.hd (List.Tot.tl revEls)], None, None) in
            let newRule = TransformAux.createRule (Namer.newSource (List.length resultRuleList) rule.name) rule.args ruleBody false rule.metaArgs in 
            let newElem = TransformAux.createDefaultElem (PRef(newRule.name, None)) in
            let changedRule = List.rev (List.Tot.tl (List.Tot.tl revEls)) @ [newElem] in
            mon_inc_cutRule_lemma ({ rule with body = 
                            PSeq(
                                changedRule, 
                                (match rule.body with PSeq(e, a, l) -> a | _ -> None),
                                (match rule.body with PSeq(e, a, l) -> l | _ -> None)) })
                            (resultRuleList @ [newRule]) 
        else ()
*)

    val short_right_rule_lemma: 
        rule: (Rule 'a 'b) 
        -> resultRuleList:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> lengthBodyRule x <= 2) resultRuleList} 
        -> Lemma
            (requires ( True )) 
            (ensures ( List.Tot.for_all (fun x -> lengthBodyRule x <= 2) (cutRule rule resultRuleList)  ))
            (decreases %[ lengthBodyRule rule; List.length resultRuleList])
            [SMTPat ( cutRule rule resultRuleList )]
    let rec short_right_rule_lemma rule resultRuleList =
        let elements = match rule.body with PSeq(e, a, l) -> e | _ -> [] in
        if lengthBodyRule rule > 2 
        then
            let revEls = List.rev elements in 
            let ruleBody = getShortPSeq revEls in
            let newRule = TransformAux.createRule (Namer.newSource (List.length resultRuleList) rule.name) rule.args ruleBody false rule.metaArgs in 
            let newElem = TransformAux.createDefaultElem (PRef(newRule.name, None)) in
            let changedRule = List.rev (List.Tot.tl (List.Tot.tl revEls)) @ [newElem] in
            short_right_rule_lemma ({ rule with body = 
                            PSeq(
                                changedRule, 
                                (match rule.body with PSeq(e, a, l) -> a | _ -> None),
                                (match rule.body with PSeq(e, a, l) -> l | _ -> None)) })
                            ([])
        else admit()

(*
    val short_right_rule_lemma: 
        rule: (Rule 'a 'b) 
        -> resultRuleList:(list (Rule 'a 'b))
        -> Lemma
            (requires ( True )) 
            (ensures ( List.Tot.for_all (fun x -> lengthBodyRule x <= 2) (cutRule rule resultRuleList)  ))
            (decreases %[ lengthBodyRule rule; List.length resultRuleList])
            [SMTPat ( cutRule rule resultRuleList )]
    let rec short_right_rule_lemma rule resultRuleList =
        let elements = match rule.body with PSeq(e, a, l) -> e | _ -> [] in
        if lengthBodyRule rule > 2 
        then 
            let revEls = List.rev elements in 
            let ruleBody = PSeq([List.Tot.hd revEls; List.Tot.hd (List.Tot.tl revEls)], None, None) in
            let newRule = TransformAux.createRule (Namer.newSource (List.length resultRuleList) rule.name) rule.args ruleBody false rule.metaArgs in 
            let newElem = TransformAux.createDefaultElem (PRef(newRule.name, None)) in
            let changedRule = List.rev (List.Tot.tl (List.Tot.tl revEls)) @ [newElem] in
            short_right_rule_lemma ({ rule with body = 
                            PSeq(
                                changedRule, 
                                (match rule.body with PSeq(e, a, l) -> a | _ -> None),
                                (match rule.body with PSeq(e, a, l) -> l | _ -> None)) })
                            (resultRuleList @ [newRule]) 
        else () (* Как я понимаю, тут какие-то проблемы с resultRuleList *)
*)

    val short_right_rules_lemma: r: list (Rule 'a 'b) ->
        Lemma
            (requires True) 
            (ensures (List.Tot.for_all (fun x -> lengthBodyRule x <= 2) (splitLongRule r) ))
    let rec short_right_rules_lemma r =
        match r with 
        | [] -> ()
        | hd::tl -> admit() (* don't works. short_right_rule_lemma hd [] ; short_right_rules_lemma tl *)



//-- dummy --
(*
    val cutRule_short_rule: rule: (Rule 'a 'b) -> resultRuleList:(list (Rule 'a 'b)){List.Tot.for_all (fun x -> lengthBodyRule x <= 2) resultRuleList} ->
        Lemma
            (requires ( lengthBodyRule rule <= 2 )) 
            (ensures ( List.length (cutRule rule resultRuleList) = List.length resultRuleList + 1 ))
    let rec cutRule_short_rule rule resultRuleList = ()
*)
(*
    val mon_inc_splitLongRule_lemma: ruleList: list (Rule 'a 'b) ->
        Lemma
            (requires ( True )) 
            (ensures ( List.length (splitLongRule ruleList) >= List.length ruleList ))
            [SMTPat ( splitLongRule ruleList )]
    let rec mon_inc_splitLongRule_lemma ruleList =
        match ruleList with
        | [] -> ()
        | rule::tl -> 
            if lengthBodyRule rule > 2 
            then admit()                                //--(mon_inc_cutRule_lemma rule []; mon_inc_splitLongRule_lemma tl)
            else mon_inc_splitLongRule_lemma tl
*)