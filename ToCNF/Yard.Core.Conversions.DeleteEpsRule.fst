module Yard.Core.Conversions.DeleteEpsRule
    open IL
    open Yard.Core
    open Yard.Core.Conversions
    open FStar.ListProperties

    val pow2: nat -> Tot nat
    let rec pow2 n = match n with 0 -> 1 | _ -> 2 * pow2 (n - 1)

    // X:List --> 2^X
    val powerset: list 'a -> Tot (list (list 'a))
    let rec powerset = function
        | [] -> [[]]
        | x::xs -> List.Tot.collect (fun subset -> [subset; List.Tot.append [x] subset]) (powerset xs)

    val powSetLemma1: l:(list 'a) -> 
        Lemma 
            (requires True) 
            (ensures (List.length (powerset l) <= pow2 (List.length l)))
            [SMTPat (powerset l)]
    let rec powSetLemma1 l = 
        match l with  
        | [] -> ()
        | hd::tl -> admit ()

    // A => C1,...,Cn where forall i in [1..n] : Ci => eps
    val isEpsWeakGen: list string -> rule: Rule 'a 'b {Helpers.isPSeq rule.body} -> Tot bool
    let isEpsWeakGen nonEpsNameList rule  =
        match rule.body with PSeq(elements,_,_) ->
            List.Tot.for_all 
                (fun elem -> 
                    match elem.rule with 
                    | PRef(s,_) -> not (List.Tot.contains s.text nonEpsNameList) 
                    | _ -> false 
                ) elements

    val nonEpsGenHelper: list (rule: Rule 'a 'b {Helpers.isPSeq rule.body}) -> nonEpsGen: list string -> Tot (list string) (decreases %[List.length nonEpsGen])
    let rec nonEpsGenHelper ruleList nonEpsGenNameList =
        let epsGen = 
            Helpers.removeDuplicates (
                List.Tot.map Helpers.getLeftPart (
                    List.Tot.filter (isEpsWeakGen nonEpsGenNameList) 
                        ruleList)) in 

        let (newNonEpsGenNameList: list string {List.length newNonEpsGenNameList <= List.length nonEpsGenNameList}) = 
            Helpers.except epsGen nonEpsGenNameList in
        
        if (List.length newNonEpsGenNameList = List.length nonEpsGenNameList)  // TODO: доказать: (длины листов равны => они ещё и поэлементно равны)
        then nonEpsGenNameList
        else nonEpsGenHelper ruleList (newNonEpsGenNameList)


    // ruleList -> [Ai => eps]
    val getEpsRuleNameList: list (rule: Rule 'a 'b {Helpers.isPSeq rule.body}) -> Tot (list string)
    let getEpsRuleNameList ruleList =
        let getEpsRuleName rule = if (Helpers.isEpsRule rule) then [rule.name.text] else [] in
        List.Tot.collect getEpsRuleName ruleList

    // ruleList -> [Ai =>* eps]
    val getEpsGenRuleNameList: list (rule: Rule 'a 'b {Helpers.isPSeq rule.body}) -> Tot (list string) 
    let getEpsGenRuleNameList ruleList =
        let allNonterm = Helpers.removeDuplicates (List.Tot.map Helpers.getLeftPart ruleList) in 
        let epsRuleList = getEpsRuleNameList ruleList in 
        let epsGenRuleList = Helpers.except (nonEpsGenHelper ruleList (Helpers.except epsRuleList allNonterm)) allNonterm in
        epsGenRuleList


    val mapLemma: f:('a -> Tot 'b) -> l:list 'a -> 
        Lemma 
            (requires True) 
            (ensures (List.length (List.Tot.map f l) = (List.length l)))
            [SMTPat (List.Tot.map f l)]
    let rec mapLemma f l = 
        match l with  
        | [] -> ()
        | x::xs -> mapLemma f xs


    val newRules: list string -> rule: Rule 'a 'b {Helpers.isPSeq rule.body} -> Tot (result: list (Rule 'a 'b) {List.length result <= pow2 (List.length (Helpers.getRightPartList rule))} )
    let newRules epsGenNameList rule =
        let epsRef = List.Tot.filter (fun term -> List.Tot.contains term epsGenNameList) (Helpers.getRightPartPRefList rule) in

        let pList = Helpers.getRightPartList rule in
        let pRefList = Helpers.getRightPartPRefList rule in
        let nonEpsGeneratingTerms = List.Tot.filter (fun name -> not (List.Tot.contains name epsRef)) pList in

        let powRule = powerset pList in
        
        let powRulesTrue = List.Tot.filter (fun listName -> List.Tot.for_all (fun nET -> List.Tot.contains nET listName) nonEpsGeneratingTerms) powRule in
        
        let packString = 
            List.Tot.map (fun powRule -> 
                    List.Tot.map (fun str ->
                        if List.Tot.contains str pRefList
                        then TransformAux.createSimpleElem (PRef(new_Source0(str), None)) None
                        else TransformAux.createSimpleElem (PToken(new_Source0(str))) None 
                    ) powRule
                ) powRulesTrue in

        let ac,lbl = match rule.body with PSeq(e, a, l) -> a,l | _ -> None,None in
        List.Tot.map (fun x -> {rule with body=PSeq(x, ac, lbl)}) packString



    val isNotEpsRule: Rule 'a 'b -> Tot bool
    let isNotEpsRule rule = not (Helpers.isEpsRule rule)

    val deleteEpsRule: 
        list (rule: Rule 'a 'b {Helpers.isPSeq rule.body}) 
        -> Tot (list (rule: (Rule 'a 'b){isNotEpsRule rule}))
    let deleteEpsRule ruleList =
        let epsGenNameList = getEpsGenRuleNameList ruleList in
        let powRulesFlat 
            = List.Tot.collect (newRules epsGenNameList) ruleList in
        Helpers.filter isNotEpsRule powRulesFlat 


// Bonus:
// TODO: List.Tot.for_all isNotEpsRule result ==> List.isEmpty (getEpsRuleNameList ruleList)
// TODO: List.isEmpty (getEpsRuleNameList ruleList) ==> List.isEmpty (getEpsGenRuleNameList ruleList) 

    // List.Tot.for_all isNotEpsRule result ==> List.isEmpty (getEpsRuleNameList ruleList)
//    val epsGenLemma1: ruleList:list (Rule 'a 'b) -> 
//        Lemma 
//            (requires (List.Tot.for_all isNotEpsRule ruleList))
//            (ensures (List.isEmpty (getEpsRuleNameList ruleList)))
//    let rec epsGenLemma1 ruleList = 
//        match ruleList with  
//        | [] -> ()
//        | hd::tl -> admit()

    // нет [A => eps] => нет [A =>* eps]
//    val epsGenLemma2: ruleList:list (Rule 'a 'b) -> 
//        Lemma 
//            (requires (List.isEmpty (getEpsRuleNameList ruleList)))
//            (ensures (List.isEmpty (getEpsGenRuleNameList ruleList)))
//    let rec epsGenLemma2 ruleList = 
//        match ruleList with  
//        | [] -> ()
//        | hd::tl -> admit()



// TODO: Если правила короткие, то количество правил вырастает полиномиально


(*
    val maxHelper: list nat -> nat -> Tot nat
    let rec maxHelper lst acc = match lst with [] -> acc | x::xs -> maxHelper xs (if acc > x then acc else x)

    val listMax: lst: list nat {is_Cons lst} -> Tot nat
    let listMax lst = maxHelper lst (List.Tot.hd lst)

    val listSum: list nat -> Tot nat
    let rec listSum lst = match lst with [] -> 0 | x::xs -> x + listSum xs


    val listPairSum: list (p : (nat * nat) {  fst p >= snd p } ) -> Tot (res : (nat * nat) {  fst res >= snd res } )
    let rec listPairSum lst = 
        let h (x : (nat * nat) {  fst x >= snd x } ) (y : (nat * nat) {  fst y >= snd y } ): (pp : (nat * nat) {  fst pp >= snd pp } )= (fst x + fst y, snd x + snd y) in 
        match lst with 
        | [] -> (0,0) 
        | (x,y)::xs -> h (x,y) (listPairSum xs)



//    assume val flattenListLemma: l:(list (list 'a)){is_Cons l} ->
//        Lemma
//            (requires (True)) 
//            (ensures (List.Tot.length (List.Tot.flatten l) <= (List.length l) * (listMax (List.Tot.map (fun xs -> List.length xs) l) )))  

    val le: nat -> nat -> Tot bool
    let le a b = a >= b 
    
    assume val powLemma1: n:nat ->
        Lemma
            (requires (True)) 
            (ensures (forall (m:nat). m <= n ==> pow2 m <= pow2 n))
            [SMTPat (pow2 n)]

    assume val powLemma2: n:nat ->
        Lemma
            (requires (True)) 
            (ensures (n < pow2 n))
            [SMTPat (pow2 n)]

    assume val maxLemma1: l: list nat {is_Cons l} ->
        Lemma
            (requires (True)) 
            (ensures (List.Tot.for_all (le (listMax l ) ) l ) )
            [SMTPat (listMax l)]    

    assume val maxLemma2: l: list nat {is_Cons l} ->
        Lemma
            (requires (True)) 
            (ensures (forall x. List.mem x l ==> x <= listMax l))
            [SMTPat (listMax l)]

    //let lenRigthPart (rule: (Rule _ _) {Helpers.isPSeq rule.body && List.mem rule ruleList}
    let lenRigthPart (rule: (Rule _ _) {Helpers.isPSeq rule.body}) 
        = List.length (Helpers.getRightPartList rule)  

    assume val maxLemma3: ruleList: list (rule: Rule 'a 'b {Helpers.isPSeq rule.body}) {is_Cons ruleList} ->
        Lemma
            (requires (True)) 
            (ensures (forall rule. List.mem rule ruleList ==> (lenRigthPart rule) <= listMax (List.Tot.map lenRigthPart ruleList))) 
            [SMTPat (listMax (List.Tot.map lenRigthPart ruleList))]

    //val deleteEpsRule: list (rule: Rule 'a 'b {Helpers.isPSeq rule.body}) -> Tot (result: list (rule: (Rule 'a 'b){isNotEpsRule rule}))
    //val deleteEpsRule: ruleList: list (rule: Rule 'a 'b {Helpers.isPSeq rule.body}) {is_Cons ruleList} -> list (rule: (Rule 'a 'b) {Helpers.isPSeq rule.body})
    //val deleteEpsRule: ruleList: list (rule: Rule 'a 'b {Helpers.isPSeq rule.body}){is_Cons ruleList} -> list (rule: (Rule 'a 'b) {Helpers.isPSeq rule.body})
    //let deleteEpsRule ruleList =
    //    let epsGenNameList = getEpsGenRuleNameList ruleList in

    //    let maxLenRigth = listMax (List.Tot.map lenRigthPart ruleList) in
    //    assert (forall rule. List.mem rule ruleList  ==> lenRigthPart rule <= maxLenRigth ); 
        //let amountPowRul (rule: (Rule _ _) {Helpers.isPSeq rule.body && List.mem rule ruleList} ): (res: nat { res <= pow2 maxLenRigth } ) 
        //    = List.length (newRules epsGenNameList rule) in
    //    assert (  forall rule. List.mem rule ruleList ==> List.length (newRules epsGenNameList rule) <= pow2 maxLenRigth ) ;
    //    let powRulesFlat 
    //        = List.Tot.collect (newRules epsGenNameList) ruleList in
        //Helpers.filter isNotEpsRule powRulesFlat 
    //    ruleList

*)


(*
    val upperBound: ruleList: list (rule: Rule 'a 'b {Helpers.isPSeq rule.body}) {is_Cons ruleList} -> Tot nat 
    let upperBound ruleList =
        let n = List.Tot.length ruleList in
        let lenRigthPart (rule: Rule 'a 'b {Helpers.isPSeq rule.body}) : nat = List.Tot.length (Helpers.getRightPartList rule) in
        let lens = List.Tot.map lenRigthPart ruleList in
        if (List.length lens > 0) then n * (pow2 (max lens)) else 0
*)


(*
    val powSetLemma1: l:(list 'a) -> 
        Lemma 
            (requires True) 
            (ensures (List.length l <= List.length (powerset l)))
    let rec powSetLemma1 l = 
        match l with  
        | [] -> ()
        | x::xs -> admit ()
*)


