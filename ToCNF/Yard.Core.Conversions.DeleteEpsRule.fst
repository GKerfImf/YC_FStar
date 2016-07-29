module Yard.Core.Conversions.DeleteEpsRule
    open IL

    val createSimpleElem: #a:Type -> #b:Type -> production a b -> option a -> Tot (elem a b)
    let createSimpleElem #a #b rulProd bind = 
        { omit = false; rule = rulProd; binding = bind; checker = None }

    val pow2: nat -> Tot nat
    let rec pow2 n = match n with 
        | 0 -> 1 | _ -> op_Multiply 2 (pow2 (n - 1))

    // X:List --> 2^X
    val powerset: #a:Type -> list a -> Tot (list (list a))
    let rec powerset #a = function
        | [] -> [[]]
        | x::xs -> List.Tot.collect (fun subset -> [subset; List.Tot.append [x] subset]) (powerset xs)

    val powSetLemma1: #a:Type -> l:(list a) ->
        Lemma 
            (requires True) 
            (ensures (List.Tot.length (powerset l) <= pow2 (List.Tot.length l)))
            [SMTPat (powerset l)]
    let rec powSetLemma1 #a l = 
        match l with  
        | [] -> ()
        | hd::tl -> admit ()

    // A => C1,...,Cn where forall i in [1..n] : Ci => eps
    val isEpsWeakGen: #a:Type -> #b:Type -> list string -> rule0: rule a b {Helpers.isPSeq rule0.body} -> Tot bool
    let isEpsWeakGen #a #b nonEpsNameList rule0 =
        match rule0.body with 
            | PSeq(elements,_,_) ->
                List.Tot.for_all 
                    (fun elem -> 
                        match elem.rule with 
                        | PRef(s,_) -> not (List.Tot.contains s.text nonEpsNameList) 
                        | _ -> false 
                    ) elements

    val nonEpsGenHelper: #a:eqtype -> #b:eqtype -> list (rule0: rule a b {Helpers.isPSeq rule0.body}) -> nonEpsGen: list string -> Tot (list string) (decreases %[List.Tot.length nonEpsGen])
    let rec nonEpsGenHelper #a #b ruleList nonEpsGenNameList =
        let epsGen = 
            Helpers.removeDuplicates (
                List.Tot.map Helpers.getLeftPart (
                    List.Tot.filter (isEpsWeakGen nonEpsGenNameList) 
                        ruleList)) in 

        let (newNonEpsGenNameList: list string {List.Tot.length newNonEpsGenNameList <= List.Tot.length nonEpsGenNameList}) = 
            Helpers.except epsGen nonEpsGenNameList in
        
        if (List.Tot.length newNonEpsGenNameList = List.Tot.length nonEpsGenNameList)  // TODO: доказать: (длины листов равны => они ещё и поэлементно равны)
        then nonEpsGenNameList
        else nonEpsGenHelper ruleList (newNonEpsGenNameList)


    // ruleList -> [Ai => eps]
    val getEpsRuleNameList: #a:Type -> #b:Type -> list (rule0: rule a b {Helpers.isPSeq rule0.body}) -> Tot (list string)
    let getEpsRuleNameList #a #b ruleList =
        let getEpsRuleName rule = if (Helpers.isEpsRule rule) then [rule.name.text] else [] in
        List.Tot.collect getEpsRuleName ruleList

    // ruleList -> [Ai =>* eps]
    val getEpsGenRuleNameList: #a:eqtype -> #b:eqtype -> list (rule0: (rule a b) {Helpers.isPSeq rule0.body}) -> Tot (list string) 
    let getEpsGenRuleNameList #a #b ruleList =
        let allNonterm = Helpers.removeDuplicates (List.Tot.map Helpers.getLeftPart ruleList) in 
        let epsRuleList = getEpsRuleNameList ruleList in 
        let epsGenRuleList = Helpers.except (nonEpsGenHelper ruleList (Helpers.except epsRuleList allNonterm)) allNonterm in
        epsGenRuleList

//TODO: del, ListProp, map_lemma
    val mapLemma: f:('a -> Tot 'b) -> l:list 'a -> //'
        Lemma 
            (requires True) 
            (ensures (List.Tot.length (List.Tot.map f l) = (List.Tot.length l)))
            [SMTPat (List.Tot.map f l)]
    let rec mapLemma f l = 
        match l with  
        | [] -> ()
        | x::xs -> mapLemma f xs


//TODO: getRightPartLength
    val newRules: #a:Type -> #b:Type -> list string -> rule0: rule a b {Helpers.isPSeq rule0.body} -> Tot (result: list (rule a b) {List.Tot.length result <= pow2 (List.Tot.length (Helpers.getRightPartList rule0))} )
    let newRules #a #b epsGenNameList rule0 =
        let epsRef = List.Tot.filter (fun term -> List.Tot.contains term epsGenNameList) (Helpers.getRightPartPRefList rule0) in

        let pList = Helpers.getRightPartList rule0 in

        let pRefList = Helpers.getRightPartPRefList rule0 in

        let nonEpsGeneratingTerms = List.Tot.filter (fun name -> not (List.Tot.contains name epsRef)) pList in

        let powRule = powerset pList in
        
        let powRulesTrue = List.Tot.filter (fun listName -> List.Tot.for_all (fun nET -> List.Tot.contains nET listName) nonEpsGeneratingTerms) powRule in
        
        let packString = 
            List.Tot.map (fun powRule -> 
                    List.Tot.map (fun str ->
                        if List.Tot.contains str pRefList
                        then createSimpleElem (PRef(new_Source0(str), None)) None
                        else createSimpleElem (PToken(new_Source0(str))) None 
                    ) powRule
                ) powRulesTrue in


        let ac,lbl = match rule0.body with | PSeq(e, a, l) -> a,l | _ -> None,None in
        let tempPack x = {name = rule0.name; args = rule0.args; body=PSeq(x, ac, lbl); isStart = rule0.isStart; isPublic = rule0.isPublic; metaArgs = rule0.metaArgs} in
        List.Tot.map tempPack packString



    val isNotEpsRule: #a:Type -> #b:Type -> rule a b -> Tot bool
    let isNotEpsRule #a #b rule = not (Helpers.isEpsRule rule)


(*
    val deleteEpsRule: #a:eqtype -> #b:eqtype 
        -> list (rule0: rule a b {Helpers.isPSeq rule0.body}) 
        -> Tot (result: list (rule a b) {forall rule0. List.Tot.mem rule0 result ==> isNotEpsRule rule0})
    let deleteEpsRule #a #b ruleList =
        let epsGenNameList = getEpsGenRuleNameList ruleList in
        let powRulesFlat 
            = List.Tot.collect (newRules epsGenNameList) ruleList in
        List.Tot.filter isNotEpsRule powRulesFlat 
*)

    val max: l: list nat {is_Cons l} -> Tot nat 
    let rec max l = match l with
        | hd::[] -> hd
        | hd::tl -> 
            let mtl = max tl in 
            if mtl > hd then mtl else hd

    val sum: list nat -> Tot nat
    let rec sum l = 
        match l with 
        | [] -> 0
        | hd::tl -> hd + sum tl


    val deleteEpsRule: #a:eqtype -> #b:eqtype 
        -> list (rule0: rule a b {Helpers.isPSeq rule0.body}) 
        -> Tot (result: list (rule a b) {forall rule0. List.Tot.mem rule0 result ==> isNotEpsRule rule0})
    let deleteEpsRule #a #b ruleList =
        let epsGenNameList = getEpsGenRuleNameList ruleList in

        assume (is_Cons ruleList);


        assume (List.Tot.map List.Tot.length (List.Tot.map Helpers.getRightPartList ruleList) = List.Tot.map Helpers.getRightPartLength ruleList) ; 


        assume (forall (n:nat). n < pow2 n);

        assume (forall x l. List.Tot.mem x l ==> x <= max l);


        assume (forall (l:list nat). is_Cons l ==> sum l <= op_Multiply (List.Tot.length l) (max l) ) ;

        assume (forall (a:eqtype) (l: list (list a)).  is_Cons l ==>  List.Tot.length (List.Tot.flatten l) <=  op_Multiply (List.Tot.length l) (max (List.Tot.map List.Tot.length l)) ) ; 




        //sloooo..., but rigth 
        assume (forall (x1:nat) (x2:nat) (n:nat). x1 <= x2 ==> op_Multiply n x1 <= op_Multiply n x2);


        let powRulesMap = 
            List.Tot.map (newRules epsGenNameList) ruleList in







        //let t1 =  in
        let t2 = List.Tot.map Helpers.getRightPartLength ruleList in
        //let mt1 = max (List.Tot.map List.Tot.length powRulesMap) in
        let mt2 = max t2 in


        assert (forall rule. List.Tot.mem rule ruleList ==> List.Tot.length (newRules epsGenNameList rule) <= pow2 (List.Tot.length (Helpers.getRightPartList rule))) ; 








        assume (forall (l:list nat {is_Cons l}) (m:nat). 
            (forall (x:nat). List.Tot.mem x l ==> x <= m) ==> max l <= m); 

//        assume ( forall (a:Type) (p: a -> Tot bool) (t0: a) (t1: list a) (t2: list (list a)). 
//            (List.Tot.mem t (List.Tot.map List.Tot.length t2) ==> p t) ==>
//                List.Tot.mem t2 
//            );


        //assert ( forall t. List.Tot.mem t t1 ==> t <= mt1 );

        //assert ( forall t. List.Tot.mem t t2 ==> t <= mt2 );
        //assert ( forall t. List.Tot.mem t t2 ==> t <= pow2 mt2 );




        assume ( forall    rule. List.Tot.mem     rule                                                                        ruleList ==> List.Tot.length (newRules epsGenNameList rule) <= pow2 mt2) ; 

        assume ( forall powrule. List.Tot.mem     powrule                            (List.Tot.map (newRules epsGenNameList) ruleList) ==>                        List.Tot.length powrule <= pow2 mt2) ; 

        assume ( forall     len. List.Tot.mem     len (List.Tot.map List.Tot.length (List.Tot.map (newRules epsGenNameList) ruleList)) ==>                                            len <= pow2 mt2 );    





///
        assert ( forall t. List.Tot.mem t (List.Tot.map List.Tot.length (List.Tot.map (newRules epsGenNameList) ruleList)) ==> t <= pow2 mt2 );


        assert ( forall t. List.Tot.mem t (List.Tot.map List.Tot.length powRulesMap) ==> t <= pow2 mt2 );


        assert ( max (List.Tot.map List.Tot.length powRulesMap) <= pow2 mt2) ;




        let powRulesFlat = List.Tot.flatten powRulesMap in
        //assert (List.Tot.length powRulesFlat <= op_Multiply (List.Tot.length powRulesMap) maxrpPow );
        //assert ( List.Tot.length powRulesFlat <= op_Multiply (List.Tot.length powRulesMap) (pow2 maxrp) );


        let ans = List.Tot.filter isNotEpsRule powRulesFlat in
        //assert ( List.Tot.length ans <= List.Tot.length powRulesFlat );
        //assert ( List.Tot.length ans <= op_Multiply (List.Tot.length powRulesMap) (pow2 maxrp) );
        //assert ( List.Tot.length ans <= op_Multiply (List.Tot.length ruleList) (pow2 (max (List.Tot.map List.Tot.length (List.Tot.map Helpers.getRightPartList ruleList)))) );
        assert ( List.Tot.length ans <= op_Multiply (List.Tot.length ruleList) (pow2 (max (List.Tot.map Helpers.getRightPartLength ruleList))));

        ans




(*


    val deleteEpsRuleLemma: #a:eqtype -> #b:eqtype 
        -> rl:list (rule0: rule a b {Helpers.isPSeq rule0.body}) ->
        Lemma 
            (requires True) 
            (ensures (                List.Tot.length (deleteEpsRule rl) < 100                     ))
    let rec deleteEpsRuleLemma #a #b rl =








        ()


*)        



// Bonus:
// TODO: List.Tot.for_all isNotEpsRule result ==> List.isEmpty (getEpsRuleNameList ruleList)
// TODO: List.isEmpty (getEpsRuleNameList ruleList) ==> List.isEmpty (getEpsGenRuleNameList ruleList) 

    // List.Tot.for_all isNotEpsRule result ==> List.isEmpty (getEpsRuleNameList ruleList)
//    val epsGenLemma1: #a:eqtype -> #b:eqtype 
//        -> ruleList:list (rule a b) -> 
//        Lemma 
//            (requires (ruleList: list (rule a b) {forall rule0. List.Tot.mem rule0 ruleList ==> isNotEpsRule rule0}))
//            (ensures (List.Tot.isEmpty (getEpsRuleNameList ruleList)))
//    let rec epsGenLemma1 #a #b ruleList = 
//        match ruleList with  
//        | [] -> ()
//        | hd::tl -> epsGenLemma1 tl

    // нет [A => eps] => нет [A =>* eps]
//    val epsGenLemma2: #a:eqtype -> #b:eqtype 
//        -> ruleList:list (rule a b) -> 
//        Lemma 
//            (requires (List.Tot.isEmpty (getEpsRuleNameList ruleList)))
//            (ensures (List.Tot.isEmpty (getEpsGenRuleNameList ruleList)))
//    let rec epsGenLemma2 #a #b ruleList = 
//        match ruleList with  
//        | [] -> ()
//        | hd::tl -> epsGenLemma2 tl




    //let deleteEpsRule ruleList =
    //    let epsGenNameList = getEpsGenRuleNameList ruleList in

    //    let maxLenRigth = listMax (List.Tot.map lenRigthPart ruleList) in
    //    assert (forall rule. List.mem rule ruleList  ==> lenRigthPart rule <= maxLenRigth ); 
        //let amountPowRul (rule: (Rule _ _) {Helpers.isPSeq rule.body && List.mem rule ruleList} ): (res: nat { res <= pow2 maxLenRigth } ) 
        //    = List.Tot.length (newRules epsGenNameList rule) in
    //    assert (  forall rule. List.mem rule ruleList ==> List.Tot.length (newRules epsGenNameList rule) <= pow2 maxLenRigth ) ;
    //    let powRulesFlat 
    //        = List.Tot.collect (newRules epsGenNameList) ruleList in
        //Helpers.filter isNotEpsRule powRulesFlat 
    //    ruleList







(*



        let epsGenNameList = getEpsGenRuleNameList ruleList in


        assume (forall (a:Type) (b:Type) (rule0: rule a b {Helpers.isPSeq rule0.body} ). Helpers.getRightPartLength rule0 = List.Tot.length (Helpers.getRightPartList rule0) );


        assume (List.Tot.map List.Tot.length (List.Tot.map Helpers.getRightPartList ruleList) = List.Tot.map Helpers.getRightPartLength ruleList) ; 



        let maxRPold = max (List.Tot.map List.Tot.length (List.Tot.map Helpers.getRightPartList ruleList)) in


        assume (forall x l. List.Tot.mem x l ==> x <= max l);
        assume (forall x l. List.Tot.mem x l ==> x <= max l);


        assume (forall rule. List.Tot.mem rule ruleList ==> 
            List.Tot.length (Helpers.getRightPartList rule) <= maxRPold
        ) ;






        assume ( forall (m:nat) (n:nat). m <= n ==> pow2 m <= pow2 n );

        assume ( forall (n:nat). n < pow2 n    );



        assume (forall (l:list nat). sum l <= op_Multiply (List.Tot.length l) (max l) ) ;

        assume (forall (a:eqtype) (l: list (list a)). List.Tot.length (List.Tot.flatten l)          <=  op_Multiply (List.Tot.length l) (max (List.Tot.map List.Tot.length l)) ) ; 





        let powRulesMap = 
            List.Tot.map (newRules epsGenNameList) ruleList in

        //let powRulesMapLength =  in



        //Ok
        assume (forall rule. List.Tot.mem rule ruleList ==> 
            List.Tot.length (newRules epsGenNameList rule) <= pow2 (List.Tot.length (Helpers.getRightPartList rule)) 
        ) ;

        let maxrp = max (List.Tot.map List.Tot.length (List.Tot.map Helpers.getRightPartList ruleList)) in

        //Ok
        assume (forall rule. List.Tot.mem rule ruleList ==> 
            List.Tot.length (newRules epsGenNameList rule) <= pow2 maxrp
        ) ;


        //Ok
        assume (forall rule. List.Tot.mem rule ruleList ==> 
            List.Tot.length (newRules epsGenNameList rule) <= pow2 maxrp
        ) ;




        let maxrpPow = max (List.Tot.map List.Tot.length powRulesMap)  in

        //Ok
        assume (forall lpowrule. List.Tot.mem lpowrule (List.Tot.map List.Tot.length powRulesMap) ==> 
            lpowrule <= maxrpPow
        ) ;

        //false
        assume (maxrpPow <= pow2 maxrp) ;


        
        //assume (List.Tot.length powRulesMap = List.Tot.length ruleList); //Ok



        assume (forall (x1:nat) (x2:nat) (n:nat). x1 <= x2 ==> op_Multiply n x1 <= op_Multiply n x2);


        let powRulesFlat = List.Tot.flatten powRulesMap in
        //assert (List.Tot.length powRulesFlat <= op_Multiply (List.Tot.length powRulesMap) maxrpPow );
        //assert ( List.Tot.length powRulesFlat <= op_Multiply (List.Tot.length powRulesMap) (pow2 maxrp) );


        let ans = List.Tot.filter isNotEpsRule powRulesFlat in
        //assert ( List.Tot.length ans <= List.Tot.length powRulesFlat );
        //assert ( List.Tot.length ans <= op_Multiply (List.Tot.length powRulesMap) (pow2 maxrp) );
        assert ( List.Tot.length ans <= op_Multiply (List.Tot.length ruleList) (pow2 maxrp) );

        ans


*)