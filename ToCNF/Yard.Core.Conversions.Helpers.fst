module Yard.Core.Conversions.Helpers
    open IL

    val isPToken: Production 'a 'b -> Tot bool
    let isPToken prod = match prod with PToken(_) -> true | _ -> false

    val isPRef: Production 'a 'b -> Tot bool
    let isPRef prod = match prod with PRef(_) -> true | _ -> false

    val isPSeq: Production 'a 'b -> Tot bool
    let isPSeq prod = match prod with PSeq(_) -> true | _ -> false


    val isEpsRule: Rule 'a 'b -> Tot bool
    let isEpsRule rule = match rule.body with PSeq([], _, _) -> true | _ -> false

    val isPTokenRule: rule: Rule 'a 'b -> Tot bool
    let isPTokenRule rule = 
        match rule.body with
        | PSeq(elements,_,_) -> List.length elements = 1 && isPToken (List.Tot.hd elements).rule
        | _ -> false


    val getLeftPart: rule: Rule 'a 'b -> Tot string
    let getLeftPart rule = rule.name.text

    val getRightPartList: Rule 'a 'b -> Tot (list string)
    let getRightPartList rule = 
        match rule.body with
        | PSeq(elements,_,_) -> 
            List.Tot.collect (fun elem -> match elem.rule with | PRef(s,_) | PToken(s) -> [s.text] | _ -> []) elements
        | _ -> [] // Тут мы никогда не появляемся

    val getRightPartPRefList: Rule 'a 'b -> Tot (list string)
    let getRightPartPRefList rule = 
        match rule.body with
        | PSeq(elements,_,_) -> 
            List.Tot.collect (fun elem -> match elem.rule with PRef(s,_) -> [s.text] | _ -> []) elements
        | _ -> [] // Тут мы никогда не появляемся

    // (List.filter f list).length <= list.length
    val filterLengthLemma: f:('a -> Tot bool) -> l:(list 'a) -> 
        Lemma 
            (requires True) 
            (ensures (List.length (List.Tot.filter f l)) <= List.length l) 
            [SMTPat (List.Tot.filter f l)]
    let rec filterLengthLemma f l = 
        match l with  
        | [] -> ()
        | hd::tl -> filterLengthLemma f tl

    val except: list string -> original:list string -> Tot (filtered:list string {List.length filtered <= List.length original}) 
    let except itemsToExclude lst = 
        List.Tot.filter (fun el -> not (List.Tot.contains el itemsToExclude)) lst

    val removeDuplicates: list 'a -> Tot (list 'a)
    let removeDuplicates lst = 
        let helpRemDup item acc =
            match acc with 
            | [] -> [item]
            | _ -> if List.existsb (fun x -> x = item) acc then acc else item::acc in 
        List.Tot.fold_right helpRemDup lst []