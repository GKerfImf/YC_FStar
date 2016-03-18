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


    //type ConsCons 'a = l:(list 'a){is_Cons l && is_Cons (List.Tot.tl l)} 
    //assume val revListLengthGt2: lst:(list (elem 'a 'b)){List.length lst > 2} -> Tot ( l:(list (elem 'a 'b)){is_Cons l && is_Cons (List.Tot.tl l)} )
    //let revListLengthGt2 lst = List.Tot.rev lst


    val lenBodyProd: Rule 'a 'b -> Tot int
    let lenBodyProd rule = List.length (match rule.body with PSeq(e, a, l) -> e | _ -> [])

    val cutRule:  rule : (Rule 'a 'b) -> rl:(list (Rule 'a  'b)) -> Tot (list (Rule 'a 'b)) (decreases %[ lenBodyProd rule; List.length rl])
    let rec cutRule  (rule: Rule _ _) (resultRuleList: list (Rule _ _))= 

        let elements = match rule.body with PSeq(e, a, l) -> e | _ -> [] in

        if List.length elements > 2 then

            //TODO: После List.Tot.rev забыл, что elements длиннее, чем 2
            //После SMTPat (List.Tot.rev l) забывать не перестал
            //Но List.rev + SMTPat (List.rev l) помогло

            let revEls = List.rev elements in 

            let ruleBody = PSeq([List.Tot.hd revEls; List.Tot.hd (List.Tot.tl revEls)], None, None) in

            let newRule = TransformAux.createRule (Namer.newSource (List.length resultRuleList) rule.name) rule.args ruleBody false rule.metaArgs in 
 
            let newElem = TransformAux.createDefaultElem (PRef(newRule.name, None)) in

            let changedRule = List.rev (List.Tot.tl (List.Tot.tl revEls)) @ [newElem] in
 
            cutRule ({ rule with body = 
                            PSeq(
                                changedRule, 
                                (match rule.body with PSeq(e, a, l) -> a | _ -> None),
                                (match rule.body with PSeq(e, a, l) -> l | _ -> None)) })
                    (resultRuleList @ [newRule]) 
                    
        else
            resultRuleList @ [{ rule with name = Namer.newSource (List.length resultRuleList) rule.name}]

    val splitLongRule: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
    let splitLongRule ruleList = List.Tot.collect (fun rule -> cutRule rule []) ruleList


    val length_body: Rule 'a 'b -> Tot nat
    let length_body rule = match rule.body with PSeq(e, a, l) -> List.length e | _ -> 0

    assume val short_right_rules_lemma: r: list (Rule 'a 'b) ->
        Lemma
            (requires True) 
            (ensures (List.Tot.for_all (fun x -> x<=2) (List.Tot.map length_body (splitLongRule r))))
