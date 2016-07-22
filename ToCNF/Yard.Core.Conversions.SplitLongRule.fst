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
    let getShortPSeq revEls = PSeq([List.Tot.hd revEls; List.Tot.hd (List.Tot.tl revEls)], None, None)
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
        -> elems1: list (elem a b ) -> elems2: list (elem a b )
        -> Lemma 
            (requires (List.Tot.length elems2 = 1)) 
            (ensures ( List.Tot.length (List.Tot.append elems1 elems2) = (List.Tot.length elems1) + 1)  )
            [SMTPat (List.Tot.append elems1 elems2)]      
    let rec append_SingletonL #a #b elems1 elems2 = match elems1 with
      | [] -> ()
      | hd::tl -> append_SingletonL tl elems2   

    val appendShort: #a:eqtype -> #b:eqtype
        -> acc: shortRuleList a b
        -> item: rule a b {isRightPartLengthLE2 item}
        -> Tot (shortRuleList a b)
    let appendShort #a #b acc item = List.Tot.append acc [item]
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
        -> rule0 : (rule a b) 
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
            cutRule (appendShort resultRuleList newRule) ({ rule with body = PSeq(changedRule, ac,lbl) } ) 
        else
            appendShort resultRuleList ({ rule with name = newSource (List.Tot.length resultRuleList) rule.name})    

//--------------------------------------------------------

    val collect_ShortRulesL: #a:eqtype -> #b:eqtype
        -> f: (rule a b -> Tot (shortRuleList a b))
        -> rl: list (rule a b)
        -> Lemma 
            (requires True) 
            (ensures (forall rule. List.Tot.mem rule (List.Tot.collect f rl) ==> isRightPartLengthLE2 rule))
            [SMTPat (List.Tot.collect f rl)]      
    let rec collect_ShortRulesL #a #b f rl = match rl with
      | [] -> ()
      | hd::tl -> collect_ShortRulesL f tl   

    val splitLongRule: #a:eqtype -> #b:eqtype
        -> list (rule a b) -> Tot (shortRuleList a b)
    let splitLongRule #a #b ruleList = 
        List.Tot.collect (cutRule []) ruleList      


		
(*

		
	val append_ShortRules: 
		rule1:(list (rule 'a  'b)) {List.Tot.for_all isRightPartLengthLE2 rule1} 
        -> rule2:(list (rule 'a  'b)) {List.Tot.for_all isRightPartLengthLE2 rule2} 
        -> Tot (result:(list (rule 'a  'b)){List.Tot.for_all isRightPartLengthLE2 result})
	let rec append_ShortRules rule1 rule2 = match rule1 with
	  | [] -> rule2
	  | hd::tl -> hd::append_ShortRules tl rule2
  
	val collect_ShortRules: 
		((rule 'a  'b) -> Tot (l:(list (rule 'a  'b)){List.Tot.for_all isRightPartLengthLE2 l} ))
		-> list (rule 'a  'b) 		
		-> Tot (result:(list (rule 'a  'b)){List.Tot.for_all isRightPartLengthLE2 result})
	let rec collect_ShortRules f l = match l with
		| [] -> []
		| hd::tl -> append_ShortRules (f hd) (collect_ShortRules f tl)
	

    val splitLongRule: 
		ruleList : list (rule 'a 'b) 
	    -> Tot (result:(list (rule 'a 'b)){List.Tot.for_all isRightPartLengthLE2 result})
    let splitLongRule ruleList = collect_ShortRules (fun rule -> cutRule rule []) ruleList		
*)



(*
    val heightBodyEl: elem 'a 'b -> Tot int
    val heightBodyEls: list (elem 'a 'b) -> Tot int
                    
    let rec heightBodyEls elements = 
        match elements with             
            | hd :: tl -> heightBodyEl hd + heightBodyEls tl                
            | _ -> 0
    and heightBodyEl element = 
        match element.rule with
        | PSeq(e, _, _) -> 1 + (heightBodyEls e)
        | _ -> 0        
*)       

(*
    assume val newSourceLemma:  
        n:int -> source:Source ->  
        Lemma (source <> newSource n source)

    assume val injectiveNewSource: 
        source1:Source -> source2:Source ->
        Lemma   (requires (source1 <> source2))
                (ensures (forall n m. (newSource n source1 <> newSource m source2)))
*)


//    val createRule:
//        source 
//        -> list 'a //'
//        -> body:(production 'a 'b){Helpers.getPSeqBodyLength body <= 2}
//        -> bool 
//        -> list 'a //'
//        -> Tot (rule0:(rule 'a 'b){isRightPartLengthLE2 rule0})
//    let createRule name args body mArgs = 
//        { name = name; args = args; body = body; isStart = false; metaArgs = mArgs; isPublic = false }
