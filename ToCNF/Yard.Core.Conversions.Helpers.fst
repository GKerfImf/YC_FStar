module Yard.Core.Conversions.Helpers
    open IL

    val isPToken: #a:Type -> #b:Type
        -> production a b -> Tot bool
    let isPToken #a #b prod = match prod with 
        | PToken(_) -> true 
        | _ -> false

    val isPRef: #a:Type -> #b:Type
        -> production a b -> Tot bool
    let isPRef #a #b prod = match prod with 
        | PRef(_) -> true 
        | _ -> false

    val isPSeq: #a:Type -> #b:Type
        -> production a b -> Tot bool
    let isPSeq #a #b prod = match prod with 
        | PSeq(_) -> true 
        | _ -> false


    val isEpsRule: #a:Type -> #b:Type
        -> rule a b -> Tot bool
    let isEpsRule #a #b rule0 = match rule0.body with 
        | PSeq([], _, _) -> true 
        | _ -> false

    val isPTokenRule: #a:Type -> #b:Type
        -> rule0: (rule a b) {isPSeq rule0.body} -> Tot bool
    let isPTokenRule #a #b rule0 = match rule0.body with 
        | PSeq(elements,_,_) -> List.Tot.length elements = 1 && isPToken (List.Tot.hd elements).rule


    val getLeftPart: #a:Type -> #b:Type
        -> rule0: rule a b -> Tot string
    let getLeftPart #a #b rule0 = rule0.name.text

    val getRightPartList: #a:Type -> #b:Type
        -> rule: rule a b {isPSeq rule.body} -> Tot (list string)
    let getRightPartList #a #b rule = match rule.body with | PSeq(elements,_,_) -> 
            List.Tot.collect (fun elem -> match elem.rule with | PRef(s,_) | PToken(s) -> [s.text] | _ -> []) elements

    val getRightPartPRefList: #a:Type -> #b:Type
        -> rule: rule a b {isPSeq rule.body} -> Tot (list string)
    let getRightPartPRefList #a #b rule = match rule.body with | PSeq(elements,_,_) -> 
            List.Tot.collect (fun elem -> match elem.rule with | PRef(s,_) -> [s.text] | _ -> []) elements


//TODO: {isPSeq rule.body}  ------------------------------------------------
    val getPSeqBodyLength: #a:Type -> #b:Type 
        -> production a b -> Tot nat
    let getPSeqBodyLength #a #b prod = List.Tot.length (match prod with | PSeq(e, a, l) -> e | _ -> [])

    val getRightPartLength: #a:Type -> #b:Type
        -> rule a b -> Tot nat
    let getRightPartLength #a #b rule = getPSeqBodyLength rule.body
//------------------------------------------------


    val simpleRule: #a:Type -> #b:Type
        -> string -> list (elem a b) -> bool -> Tot (rule0: (rule a b) {Helpers.isPSeq rule0.body})
    let simpleRule #a #b nonTerm seq b =
        {name = new_Source0 nonTerm; args = []; body = PSeq(seq, None, None); isStart = b; isPublic = false; metaArgs = []}

    val simpleStartRule: #a:Type -> #b:Type
        -> string -> list (elem a b) -> Tot (list (rule0: (rule a b) {Helpers.isPSeq rule0.body}))
    let simpleStartRule #a #b nonTerm seq = [simpleRule nonTerm seq true]

    val simpleNotStartRule: #a:Type -> #b:Type
        -> string -> list (elem a b) -> Tot (list (rule0: (rule a b) {Helpers.isPSeq rule0.body}))
    let simpleNotStartRule #a #b nonTerm seq = [simpleRule nonTerm seq false]
    
//------------------------------------------------

    // (List.filter f list).length <= list.length
    val filterLengthLemma: #a:eqtype -> f:(a -> Tot bool) -> l:(list a) -> 
        Lemma 
            (requires True) 
            (ensures (List.Tot.length (List.Tot.filter f l)) <= List.Tot.length l) 
            [SMTPat (List.Tot.filter f l)]
    let rec filterLengthLemma #a f l = 
        match l with  
        | [] -> ()
        | hd::tl -> filterLengthLemma f tl

    val except: list string -> original:list string -> Tot (filtered:list string {List.Tot.length filtered <= List.Tot.length original}) 
    let except itemsToExclude lst = 
        List.Tot.filter (fun el -> not (List.Tot.contains el itemsToExclude)) lst

    val removeDuplicates: #a:eqtype -> list a -> Tot (list a)
    let removeDuplicates #a lst = 
        let helpRemDup item acc = match acc with 
            | [] -> [item]
            | _ -> if List.Tot.existsb (fun x -> x = item) acc then acc else item::acc in 
        List.Tot.fold_right helpRemDup lst []


