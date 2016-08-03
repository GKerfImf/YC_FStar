module Yard.Core.Conversions.SplitLongRule
    open IL
    open Yard.Core
    open Yard.Core.Conversions
    open FStar.ListProperties

//TODO:
// 1. Add PSeq()

    val isRightPartLengthLE2: #a:Type -> #b:Type -> rule a b -> Tot bool
    let isRightPartLengthLE2 #a #b rule = Helpers.getRightPartLength rule <= 2

    type shortRuleList (a:eqtype) (b:eqtype) = ruleList: (list (rule a b)){forall rule. List.Tot.mem rule ruleList ==> isRightPartLengthLE2 rule} 
    assume HasEq_shortRuleList: forall a b. hasEq a /\ hasEq b ==> hasEq (shortRuleList a b)

//---------------------------------------------------------------------------------------------------
    val getShortPSeq:
        listRev:(list (elem 'a 'b)){List.Tot.length listRev > 2}
        -> Tot (body:(production 'a 'b){Helpers.getPSeqBodyLength body <= 2})
    let getShortPSeq revEls = PSeq([List.Tot.hd (List.Tot.tl revEls); List.Tot.hd revEls], None, None)
//---------------------------------------------------------------------------------------------------
    val append_ShortRulesL: #a:eqtype -> #b:eqtype
        -> rule1: shortRuleList a b -> rule2: shortRuleList a b
        -> Lemma 
            (requires True) 
            (ensures (forall rule. List.Tot.mem rule (List.Tot.append rule1 rule2) ==> isRightPartLengthLE2 rule))
            [SMTPat (List.Tot.append rule1 rule2)]      
    let rec append_ShortRulesL #a #b rule1 rule2 = match rule1 with
      | [] -> ()
      | hd::tl -> append_ShortRulesL tl rule2   

    val append_SingletonL: #a:eqtype -> #b:eqtype
        -> elems1: list (elem a b ) -> elems2: list (elem a b)
        -> Lemma 
            (requires (List.Tot.length elems2 = 1)) 
            (ensures ( List.Tot.length (List.Tot.append elems1 elems2) = (List.Tot.length elems1) + 1)  )
            [SMTPat (List.Tot.append elems1 elems2)]      
    let rec append_SingletonL #a #b elems1 elems2 = match elems1 with
      | [] -> ()
      | hd::tl -> append_SingletonL tl elems2   

    val appendShort: #a:eqtype -> #b:eqtype
        -> item: rule a b {isRightPartLengthLE2 item}
        -> acc: shortRuleList a b
        -> Tot (shortRuleList a b)
    let appendShort #a #b item acc = List.Tot.append [item] acc 
//---------------------------------------------------------------------------------------------------

    val newSource: int -> source -> Tot source 
    let newSource n old = {old with text = (old.text ^ (string_of_int n))}


    val createDefaultElem: production 'a 'b -> Tot (elem 'a 'b)
    let createDefaultElem rulProd = { omit = false; rule = rulProd; binding = None; checker = None }


    val createRule: rule 'a 'b -> nat -> body:(production 'a 'b){Helpers.getPSeqBodyLength body <= 2} -> Tot (rule0:(rule 'a 'b){isRightPartLengthLE2 rule0})
    let createRule rule resLen newBody = {name = newSource resLen rule.name; args = rule.args; body = newBody; isStart = false; isPublic = false; metaArgs = rule.metaArgs; }


    val rev_length: #a:Type -> l:(list a)->
        Lemma 
            (requires True) 
            (ensures (List.Tot.length (List.Tot.rev l) = List.Tot.length l)) 
            [SMTPat (List.Tot.rev l)]
    let rev_length #a l = ListProperties.rev_acc_length l []

    val tail_length: #a:Type -> l:(list a){is_Cons l} -> 
        Lemma 
            (requires True)
            (ensures (List.Tot.length (List.Tot.tl l) = (List.Tot.length l) - 1)) 
            [SMTPat (List.Tot.tl l)]
    let tail_length #a l = ()


    val cutRule: #a:eqtype -> #b:eqtype
        -> shortRuleList a b
        -> rule0 : (rule0: (rule a b) {Helpers.isPSeq rule0.body}) 
        -> Tot (shortRuleList a b) (decreases %[Helpers.getRightPartLength rule0])
    let rec cutRule #a #b resultRuleList rule  = 
        let elements = match rule.body with | PSeq(e, a, l) -> e | _ -> [] in
        if List.Tot.length elements > 2 then
            let revElements = List.Tot.rev elements in 
            //assert (List.Tot.length revElements > 2);
            let ruleBody = getShortPSeq revElements in
            let newRule = createRule rule (List.Tot.length resultRuleList) ruleBody in 
            let newElem = createDefaultElem (PRef(newRule.name, None)) in
            let changedRule = List.Tot.rev (List.Tot.tl (List.Tot.tl revElements)) @ [newElem] in
            //assert (List.Tot.length changedRule = (List.Tot.length revElements) - 1);
            let ac,lbl = match rule.body with | PSeq(e, a, l) -> a,l | _ -> None,None in
            //assert (Helpers.getRightPartLength tempRule < Helpers.getRightPartLength rule);
            cutRule (appendShort newRule resultRuleList) ({ rule with body = PSeq(changedRule, ac,lbl) } ) 
        else
            appendShort rule resultRuleList //({ rule with name = newSource (List.Tot.length resultRuleList) rule.name})    

//--------------------------------------------------------

    val collect_ShortRulesL: #a:eqtype -> #b:eqtype
        -> f: (rule a b -> Tot (shortRuleList a b))
        -> rl: list (rule0: (rule a b) {Helpers.isPSeq rule0.body})
        -> Lemma 
            (requires True) 
            (ensures (forall rule. List.Tot.mem rule (List.Tot.collect f rl) ==> isRightPartLengthLE2 rule))
            [SMTPat (List.Tot.collect f rl)]      
    let rec collect_ShortRulesL #a #b f rl = match rl with
      | [] -> ()
      | hd::tl -> collect_ShortRulesL f tl   

    val splitLongRule: #a:eqtype -> #b:eqtype
        //-> list ( rule0: (rule a b) {Helpers.isPSeq rule0.body} ) -> Tot (shortRuleList a b)
        -> list (rule a b) -> Tot (shortRuleList a b)
    let splitLongRule #a #b ruleList = 
        let (ruleList2: list ( rule0: (rule a b) {Helpers.isPSeq rule0.body} ) ) = 
            assume ( 2 < 1 );
            ruleList in
        List.Tot.collect (cutRule []) ruleList2      