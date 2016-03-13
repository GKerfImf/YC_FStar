module Yard.Core.Conversions.SplitLongRule
    open IL
    open Yard.Core
    open Yard.Core.Conversions

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