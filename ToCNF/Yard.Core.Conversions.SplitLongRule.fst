module Yard.Core.Conversions.SplitLongRule
    open IL
    open Yard.Core
    open Yard.Core.Conversions
    open FStar.ListProperties


    val newSource: n:int -> oldSource:Source -> Tot Source 
    let newSource n old = 
        ({ old with text = (old.text ^ (string_of_int n)) })

    val isRightPartLengthLE2: Rule 'a 'b -> Tot bool
    let isRightPartLengthLE2 rule = Helpers.getRightPartLength rule <= 2

    val createSimpleElem: Production 'a 'b -> option 'a -> Tot (elem 'a 'b)
    let createSimpleElem rulProd bind = 
        { omit = false; rule = rulProd; binding = bind; checker = None }

    val createDefaultElem: Production 'a 'b -> Tot (elem 'a 'b)
    let createDefaultElem rulProd = createSimpleElem rulProd None

    //используется только для создания правил длины не более 2
    val createRule: 
        Source 
        -> list 'a //'
        -> body:(Production 'a 'b){Helpers.getPSeqBodyLength body <= 2}
        -> bool 
        -> list 'a //'
        -> Tot (rule:(Rule 'a 'b){Helpers.getRightPartLength rule <= 2})
    let createRule name args body _public mArgs = 
        { name = name; args = args; body = body; isStart = _public; metaArgs = mArgs; isPublic = false }

    val rev_length: l:(list 'a)-> 
        Lemma 
            (requires True) 
            (ensures (List.length (List.rev l) = List.length l)) 
            [SMTPat (List.rev l)]
    let rev_length l = rev_acc_length l []

    val tail_length: l:(list 'a){is_Cons l}  -> 
        Lemma 
            (requires True)
            (ensures (List.length (List.Tot.tl l) = (List.length l) - 1)) 
            [SMTPat (List.Tot.tl l)]
    let tail_length l = ()
	
	val append_ShortRulesL:  
		rule1:(list (Rule 'a  'b)) {List.Tot.for_all isRightPartLengthLE2 rule1} 
        -> rule2:(list (Rule 'a  'b)) {List.Tot.for_all isRightPartLengthLE2 rule2} 
        -> Lemma 
            (requires true) 
            (ensures (List.Tot.for_all isRightPartLengthLE2 (List.Tot.append rule1 rule2))) 
            [SMTPat (List.Tot.append rule1 rule2)]		
	let rec append_ShortRulesL rule1 rule2 = match rule1 with
	  | [] -> ()
	  | hd::tl -> append_ShortRulesL tl rule2	
	
    val getShortPSeq:
        listRev:(list (elem 'a 'b)){List.length listRev > 2}
        -> Tot (body:(Production 'a 'b){Helpers.getPSeqBodyLength body <= 2})
    let getShortPSeq revEls = PSeq([List.Tot.hd revEls; List.Tot.hd (List.Tot.tl revEls)], None, None)

    val getListOfShort:
        acc:(list (Rule 'a  'b)){List.Tot.for_all isRightPartLengthLE2 acc} 
        -> item:(Rule 'a  'b){Helpers.getRightPartLength item <= 2}
        -> Tot (result:(list (Rule 'a  'b)){List.Tot.for_all isRightPartLengthLE2 result} )
    let getListOfShort acc item = List.Tot.append acc [item]
		
    val cutRule: 
        rule : (Rule 'a 'b) 
        -> resultRuleList:(list (Rule 'a  'b)){List.Tot.for_all isRightPartLengthLE2 resultRuleList} 
        -> Tot (result:(list (Rule 'a 'b)){List.Tot.for_all isRightPartLengthLE2 result} ) (decreases %[ Helpers.getRightPartLength rule])
    let rec cutRule rule resultRuleList = 
        let elements = match rule.body with PSeq(e, a, l) -> e | _ -> [] in
        if List.length elements > 2 then
            let revEls = List.rev elements in 
            let ruleBody = getShortPSeq revEls in
            let newRule = createRule (newSource (List.length resultRuleList) rule.name) rule.args ruleBody false rule.metaArgs in 
            let newElem = createDefaultElem (PRef(newRule.name, None)) in
            let changedRule = List.rev (List.Tot.tl (List.Tot.tl revEls)) @ [newElem] in

            cutRule ({ rule with body = 
                            PSeq(
                                changedRule, 
                                (match rule.body with PSeq(e, a, l) -> a | _ -> None),
                                (match rule.body with PSeq(e, a, l) -> l | _ -> None)) }) (getListOfShort resultRuleList newRule)
                    
        else
            getListOfShort resultRuleList ({ rule with name = newSource (List.length resultRuleList) rule.name})  		  	  
		
	val append_ShortRules: 
		rule1:(list (Rule 'a  'b)) {List.Tot.for_all isRightPartLengthLE2 rule1} 
        -> rule2:(list (Rule 'a  'b)) {List.Tot.for_all isRightPartLengthLE2 rule2} 
        -> Tot (result:(list (Rule 'a  'b)){List.Tot.for_all isRightPartLengthLE2 result})
	let rec append_ShortRules rule1 rule2 = match rule1 with
	  | [] -> rule2
	  | hd::tl -> hd::append_ShortRules tl rule2
  
	val collect_ShortRules: 
		((Rule 'a  'b) -> Tot (l:(list (Rule 'a  'b)){List.Tot.for_all isRightPartLengthLE2 l} ))
		-> list (Rule 'a  'b) 		
		-> Tot (result:(list (Rule 'a  'b)){List.Tot.for_all isRightPartLengthLE2 result})
	let rec collect_ShortRules f l = match l with
		| [] -> []
		| hd::tl -> append_ShortRules (f hd) (collect_ShortRules f tl)
	
	//Непонятно, почему F* сам не может вывести тип для List.Tot.collect, когда есть лемма для List.Tot.append	(append_ShortRulesL)	
    val splitLongRule: 
		ruleList : list (Rule 'a 'b) 
	    -> Tot (result:(list (Rule 'a 'b)){List.Tot.for_all isRightPartLengthLE2 result})
    let splitLongRule ruleList = collect_ShortRules (fun rule -> cutRule rule []) ruleList		




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