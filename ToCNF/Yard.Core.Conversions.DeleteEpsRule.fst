module Yard.Core.Conversions.DeleteEpsRule
    open IL
    open Yard.Core
    open Yard.Core.Conversions
    open FStar.ListProperties
    open TransformAux
    
// -- Функция для удаления эпсилон-правил -----------------------------------------------------------

// TODO: ограничение на "правильные (PSeq)" правые части 
    val isPSeq: Production 'a 'b -> Tot bool
    let isPSeq prod = match prod with PSeq(_) -> true | _ -> false

// TODO: Если правила короткие, то количество правил вырастает полиномиально
// ???

    // X:List --> 2^X
    val powerset: list string -> Tot (res: list (list string){is_Cons res})
    let rec powerset = function
        | [] -> [[]]
        | x::xs -> List.Tot.collect (fun subset -> [subset; List.Tot.append [x] subset]) (powerset xs)

    val getRightPartRuleNameList: Rule 'a 'b -> Tot (list string)
    let getRightPartRuleNameList rule = 
        match rule.body with
        | PSeq(elements,_,_) -> 
            List.Tot.collect (fun elem -> match elem.rule with | PRef(s,_) | PToken(s) -> [s.text] | _ -> []) elements
        | _ -> [] // Тут мы никогда не появляемся

    val getRightPartRulePRefNameList: Rule 'a 'b -> Tot (list string)
    let getRightPartRulePRefNameList rule = 
        match rule.body with
        | PSeq(elements,_,_) -> 
            List.Tot.collect (fun elem -> match elem.rule with PRef(s,_) -> [s.text] | _ -> []) elements
        | _ -> [] // Тут мы никогда не появляемся

    // A => C1,...,Cn where forall i in [1..n] : Ci => eps
    val isEpsWeakGen: Rule 'a 'b -> list string -> Tot bool
    let isEpsWeakGen rule nonEpsNameList =
        match rule.body with
        | PSeq(elements,_,_) ->
            List.Tot.for_all 
                (fun elem -> 
                    match elem.rule with 
                    | PRef(s,_) -> not (List.Tot.contains s.text nonEpsNameList) 
                    | _ -> false 
                ) elements
        | _ -> false // Тут мы никогда не появляемся

    val removeDuplicates: list 'a -> Tot (list 'a)
    let removeDuplicates lst = 
        let helpRemDup item acc =
            match acc with 
            | [] -> [item]
            | _ -> if List.existsb (fun x -> x = item) acc then acc else item::acc in 
        List.Tot.fold_right helpRemDup lst []

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

    val nonEpsGenHelper: list (Rule 'a 'b) -> nonEpsGen: list string -> Tot (list string) (decreases %[List.length nonEpsGen])
    let rec nonEpsGenHelper ruleList nonEpsGenNameList =
        let epsGen = 
            removeDuplicates (List.Tot.map (fun rule -> rule.name.text)  (List.Tot.filter (fun rule -> isEpsWeakGen rule nonEpsGenNameList) ruleList)) in  
        let (newNonEpsGenNameList: list string {List.length newNonEpsGenNameList <= List.length nonEpsGenNameList}) = 
            except epsGen nonEpsGenNameList in
        
        if (List.length newNonEpsGenNameList = List.length nonEpsGenNameList)  // TODO: доказать: (длины листов равны => они ещё и поэлементно равны)
        then nonEpsGenNameList
        else nonEpsGenHelper ruleList (newNonEpsGenNameList)

    val isEpsRule: Rule 'a 'b -> Tot bool
    let isEpsRule rule = match rule.body with PSeq([], _, _) -> true | _ -> false

    val isNotEpsRule: Rule 'a 'b -> Tot bool
    let isNotEpsRule rule = not (isEpsRule rule)

    // ruleList -> [Ai => eps]
    val getEpsRuleNameList: list (Rule 'a 'b) -> Tot (list string)
    let getEpsRuleNameList ruleList =
        List.Tot.collect (fun rule -> if (isEpsRule rule) then [rule.name.text] else []) ruleList

    // ruleList -> [Ai =>* eps]
    val getEpsGenRuleNameList: list (Rule 'a 'b) -> Tot (list string) 
    let getEpsGenRuleNameList ruleList =
        let allNonterm = removeDuplicates (List.Tot.map (fun rule -> rule.name.text) ruleList) in 
        let epsRuleList = getEpsRuleNameList ruleList in 
        let epsGenRuleList = except (nonEpsGenHelper ruleList (except epsRuleList allNonterm)) allNonterm in
        epsGenRuleList

    val newRules: Rule 'a 'b -> list string -> Tot (list (Rule 'a 'b))
    let newRules rule epsRef = 
        if not (List.isEmpty epsRef) then
            let pList = getRightPartRuleNameList rule in
            let pRefList = getRightPartRulePRefNameList rule in
            let nonEpsGeneratingTerms = List.Tot.filter (fun name -> not (List.Tot.contains name epsRef)) pList in
            let powRule = (powerset pList) in
            let powRulesTrue = List.Tot.filter (fun listName -> List.Tot.for_all (fun nET -> List.Tot.contains nET listName) nonEpsGeneratingTerms) powRule in
            let packString = 
                List.Tot.collect 
                    (fun powRule -> 
                        [List.Tot.collect 
                            (fun str ->
                                if (List.Tot.contains str pRefList)
                                then [TransformAux.createSimpleElem (PRef(new_Source0(str), None)) None]
                                else [TransformAux.createSimpleElem (PToken(new_Source0(str))) None] 
                            ) powRule]
                    ) powRulesTrue in
            let ac,lbl = match rule.body with PSeq(e, a, l) -> a,l | _ -> None,None in
            List.Tot.collect (fun x -> [{rule with body=PSeq(x, ac, lbl)}]) packString
        else [rule]

    // List.forall f (List.filter f list) == true
    val filterPredLemma: f:('a -> Tot bool) -> l:(list 'a) -> 
        Lemma 
            (requires True) 
            (ensures (List.Tot.for_all f (List.Tot.filter f l)))
            [SMTPat (List.Tot.filter f l)]
    let rec filterPredLemma f l = 
        match l with  
        | [] -> ()
        | hd::tl -> filterPredLemma f tl

    val deleteEpsRule: 
        list (Rule 'a 'b) 
        -> Tot (result: (list (Rule 'a 'b)) {List.Tot.for_all isNotEpsRule result})
    let deleteEpsRule ruleList =
        let epsGenNameList = getEpsGenRuleNameList ruleList in
        let rigthPartRuleGenEpsRules rule = 
            List.Tot.filter (fun term -> List.Tot.contains term epsGenNameList) (getRightPartRulePRefNameList rule) in 
        List.Tot.filter isNotEpsRule (List.Tot.collect (fun rule -> (newRules rule (rigthPartRuleGenEpsRules rule))) ruleList)


    // Bonus:
    // TODO: List.Tot.for_all isNotEpsRule result ==> List.isEmpty (getEpsRuleNameList ruleList)
    // TODO: List.isEmpty (getEpsRuleNameList ruleList) ==> List.isEmpty (getEpsGenRuleNameList ruleList) 

    // List.Tot.for_all isNotEpsRule result ==> List.isEmpty (getEpsRuleNameList ruleList)
    val epsGenLemma1: ruleList:list (Rule 'a 'b) -> 
        Lemma 
            (requires (List.Tot.for_all isNotEpsRule ruleList))
            (ensures (List.isEmpty (getEpsRuleNameList ruleList)))
    let rec epsGenLemma1 ruleList = 
        match ruleList with  
        | [] -> ()
        | hd::tl -> admit()

    // нет [A => eps] => нет [A =>* eps]
    val epsGenLemma2: ruleList:list (Rule 'a 'b) -> 
        Lemma 
            (requires (List.isEmpty (getEpsRuleNameList ruleList)))
            (ensures (List.isEmpty (getEpsGenRuleNameList ruleList)))
    let rec epsGenLemma2 ruleList = 
        match ruleList with  
        | [] -> ()
        | hd::tl -> admit()