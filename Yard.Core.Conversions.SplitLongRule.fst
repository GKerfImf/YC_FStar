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

    assume val getListOfShort:
        acc:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> lengthBodyRule x <= 2) acc} 
        -> item:(Rule 'a  'b){lengthBodyRule item <= 2}
        -> Tot (result:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> lengthBodyRule x <= 2) result} )
    //let getListOfShort acc item = List.concat acc [item] //Что-то такое, наверное, не очень сложно придумать


    val cutRule: 
        rule : (Rule 'a 'b) 
        -> resultRuleList:(list (Rule 'a  'b)){List.Tot.for_all (fun x -> lengthBodyRule x <= 2) resultRuleList} 
        -> Tot (result:(list (Rule 'a 'b)){List.Tot.for_all (fun x -> lengthBodyRule x <= 2) result} ) (decreases %[ lengthBodyRule rule; List.length resultRuleList])
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


    //Теперь тут нужна небольшая лемма о том, что конкатенация листов с короткими правилами опять лист с короткими правилами
    val splitLongRule: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
    let splitLongRule ruleList = List.Tot.collect (fun rule -> cutRule rule []) ruleList
