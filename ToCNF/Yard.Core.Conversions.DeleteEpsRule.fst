module Yard.Core.Conversions.DeleteEpsRule
    open IL
    open Yard.Core
    open Yard.Core.Conversions
    open FStar.ListProperties
    open TransformAux
    
// -- Функция для удаления эпсилон-правил -----------------------------------------------------------

// TODO: ограничение на "правильные (PSeq)" правые части 
// TODO: Если правила короткие, то количество правил вырастает полиномиально

    // X:List --> 2^X
    val powerset: list string -> Tot (res: list (list string){is_Cons res})
    let rec powerset =
        function
        | [] -> [[]]
        | x::xs -> List.Tot.collect (fun subset -> [subset; List.Tot.append [x] subset]) (powerset xs)


    // ruleList -> [Ai => eps]
    val getEpsRuleNameList: list (Rule 'a 'b) -> Tot (list string)
    let getEpsRuleNameList ruleList =
        let isEpsRule rule = 
            match rule.body with
            | PSeq(elements, _, _) -> List.isEmpty elements
            | _ -> false in 
        List.Tot.collect (fun rule -> if (isEpsRule rule) then [rule.name.text] else []) ruleList


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
    val filterListLengthLemma: f:('a -> Tot bool) -> l:(list 'a) -> 
        Lemma 
            (requires True) 
            (ensures (List.length (List.Tot.filter f l)) <= List.length l) 
            [SMTPat (List.Tot.filter f l)]
    let rec filterListLengthLemma f l = 
        match l with  
        | [] -> ()
        | hd::tl -> filterListLengthLemma f tl

    val except: list string -> original:list string -> Tot (filtered:list string {List.length filtered <= List.length original}) 
    let except itemsToExclude lst = 
        List.Tot.filter (fun el -> not (List.Tot.contains el itemsToExclude)) lst


    val nonEpsGenHelper: list (Rule 'a 'b) -> nonEpsGen: list string -> Tot (list string) (decreases %[List.length nonEpsGen])
    let rec nonEpsGenHelper ruleList nonEpsGenNameList =
        
        let epsGen = 
            removeDuplicates (List.Tot.map (fun rule -> rule.name.text)  (List.Tot.filter (fun rule -> isEpsWeakGen rule nonEpsGenNameList) ruleList)) in  
        
        let (newNonEpsGenNameList: list string {List.length newNonEpsGenNameList <= List.length nonEpsGenNameList}) = 
            except epsGen nonEpsGenNameList in

        // TODO: доказать: (длины листов равны => они ещё и поэлементно равны)
        if (List.length newNonEpsGenNameList = List.length nonEpsGenNameList) 
        then nonEpsGenNameList
        else nonEpsGenHelper ruleList (newNonEpsGenNameList)

    // ruleList -> [Ai =>* eps]
    val getEpsGenNameList: list (Rule 'a 'b) -> Tot (list string) 
    let getEpsGenNameList ruleList =
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
            
            let temp1 = 
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
            let ans = List.Tot.collect (fun x -> [{rule with body=PSeq(x, ac, lbl)}]) temp1 in

            ans 

        else [rule]


    val deleteEpsRule: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
    let deleteEpsRule ruleList =

        let epsGenNameList = getEpsGenNameList ruleList in

        let rigthPartRuleGenEpsRules rule = 
            List.Tot.filter (fun term -> List.Tot.contains term epsGenNameList) (getRightPartRulePRefNameList rule) in 
 
        List.Tot.filter (fun r -> match r.body with PSeq([],_,_) -> false | _ -> true) (List.Tot.collect (fun rule -> (newRules rule (rigthPartRuleGenEpsRules rule))) ruleList)  





























