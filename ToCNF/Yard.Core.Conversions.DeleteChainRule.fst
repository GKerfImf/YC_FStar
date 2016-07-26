module Yard.Core.Conversions.DeleteChainRule
    open IL

    val getTextPRef: #a:Type -> #b:Type
        -> prod: production a b {Helpers.isPRef prod} -> Tot string
    let getTextPRef #a #b prod = match prod with | PRef(t,_) -> t.text

    val isUnitRule: #a:Type -> #b:Type 
        -> rule: rule a b {Helpers.isPSeq rule.body} -> Tot bool
    let isUnitRule #a #b rule = match rule.body with | PSeq(elements,_,_) -> List.Tot.length elements = 1 && Helpers.isPRef (List.Tot.hd elements).rule

    val isNonUnitRule: #a:Type -> #b:Type
        ->  rule: rule a b {Helpers.isPSeq rule.body} -> Tot bool
    let isNonUnitRule #a #b rule = not (isUnitRule rule)

//***** getChain ****************************************************************************************************************************

//  Должно быть как-то так:

//    val filterLengthLemma: f:('a -> Tot bool) -> l:(list 'a) -> 
//        Lemma 
//            (requires True) 
//            (ensures (List.Tot.length (List.Tot.filter f l)) <= List.Tot.length l) 
//            [SMTPat (List.Tot.filter f l)]
//    let rec filterLengthLemma f l =
//        match l with
//        | [] -> ()
//        | hd::tl -> filterLengthLemma f tl

//    val except: list string -> original:list string -> Tot (filtered:list string {List.Tot.length filtered <= List.Tot.length original}) 
//    let except itemsToExclude lst = 
//        List.Tot.filter (fun el -> not (List.Tot.contains el itemsToExclude)) lst

//  assume val exceptLemma0: someList:(list string) -> exclList:(list string) -> -> 
//        Lemma 
//            (requires (True)) 
//            (ensures (forall (genList: list string). List.Tot.length (except (List.Tot.append someList exclList) genList) < List.Tot.length (except exclList genList))) 
//            [SMTPat (List.Tot.append someList exclList)]

//    assume val exceptLemma1: exclList:(list string) -> genList:(list string) -> 
//      Lemma 
//          (requires True) 
//          (ensures (List.Tot.length (except exclList genList) = List.Tot.length (except (removeDuplicates exclList) genList)))
//          [SMTPat (removeDuplicates exclList)]

//  val getChain: 
//      chain: list string 
//      -> unitPairs: list (string * string) 
//      -> Tot (list string) (decreases %[List.Tot.length (except chain (List.Tot.map snd unitPairs))])
//  let rec getChain chain unitPairs =
//  
//      let temp1 = List.Tot.map snd (List.Tot.filter (fun x -> (List.Tot.contains (fst x) chain)) unitPairs) in
//  
//      let sndUnPairs = List.Tot.map snd unitPairs in
//   
//      let newChain = removeDuplicates (List.Tot.append chain temp1) in
//       
//      if List.Tot.length (except newChain (List.Tot.map snd unitPairs)) = List.Tot.length (except chain (List.Tot.map snd unitPairs)) then chain
//      else getChain newChain unitPairs
//*******************************************************************************************************************************************


    val getChainHepler: sat:nat -> chain: list string -> unitPairs: list (string * string) -> Tot (list string) (decreases %[sat])
    let rec getChainHepler sat chain unitPairs =
        let newChain = Helpers.removeDuplicates (chain @ (List.Tot.map snd (List.Tot.filter (fun x -> (List.Tot.contains (fst x) chain)) unitPairs))) in
        if newChain <> chain && sat > 0 then getChainHepler (sat - 1) newChain unitPairs else chain

    val getChain: chain: list string -> unitPairs: list (string * string) -> Tot (list string)
    let getChain chain unitPairs = getChainHepler (List.Tot.length unitPairs) chain unitPairs

    val splitUnitRule: 
        #a:Type -> #b:Type
        -> rule: (rule a b) {Helpers.isPSeq rule.body && isUnitRule rule} -> Tot (string * string)
    let splitUnitRule #a #b rule = 
        let rightPart = match rule.body with | PSeq(elems,_,_) -> getTextPRef (List.Tot.hd elems).rule in
        (rule.name.text, rightPart)
    

    val findAllUnitPair: 
        #a:eqtype -> #b:eqtype
        -> list (rule: (rule a b) {Helpers.isPSeq rule.body}) -> Tot (list (string * list string))
    let findAllUnitPair #a #b ruleList =
        let unitRules = Helpers.unliftDepType isUnitRule (List.Tot.filter isUnitRule ruleList) in
        let unitPairs = List.Tot.map splitUnitRule unitRules in
        let leftParts = Helpers.removeDuplicates (List.Tot.map fst unitPairs) in
        List.Tot.map (fun x -> (x, getChain (List.Tot.map snd (List.Tot.filter (fun y -> fst y = x) unitPairs)) unitPairs)) leftParts


    val renameRule:         
        #a:Type -> #b:Type
        -> string 
        -> rule0:(rule a b) {Helpers.isPSeq rule0.body && isNonUnitRule rule0} 
        -> Tot (rule0: (rule a b) {Helpers.isPSeq rule0.body} )
    let renameRule #a #b fstUnitPair rule0 = {rule0 with name = new_Source0 fstUnitPair}



    val newRules: 
        #a:eqtype -> #b:eqtype
        -> list (rule0: (rule a b) {Helpers.isPSeq rule0.body}) 
        -> string * (list string) 
        -> Tot (list (rule0: (rule a b) {Helpers.isPSeq rule0.body}))
    let newRules #a #b ruleList unitPair =
        let nonUnitRules = Helpers.unliftDepType isNonUnitRule (List.Tot.filter isNonUnitRule ruleList) in
        let isRuleNameEq x rule0 = rule0.name.text = x in                               
        let rulesWithName x = List.Tot.filter (isRuleNameEq x) nonUnitRules in
        let tempRules = List.Tot.collect rulesWithName (snd unitPair) in 
        List.Tot.map (renameRule (fst unitPair)) tempRules


    private val setStart: #a:eqtype -> #b:eqtype -> string  -> rule0: (rule a b) {Helpers.isPSeq rule0.body /\ isNonUnitRule rule0} -> Tot (res: (rule a b) {Helpers.isPSeq res.body /\ isNonUnitRule res})
    private let setStart #a #b sNT rule0  = if (Helpers.getLeftPart rule0 = sNT) then ({rule0 with isStart = true}) else rule0

    val deleteChainRule: #a:eqtype -> #b:eqtype
        -> ruleList: list (rule0: (rule a b) {Helpers.isPSeq rule0.body}) { is_Cons (List.Tot.filter Helpers.isStartRule ruleList) } //~> { exists rule. rule in ruleList /\ rule.isStart }
        -> Tot (lst: list (rule0: (rule a b) {Helpers.isPSeq rule0.body /\ isNonUnitRule rule0}))
    let deleteChainRule #a #b ruleList = 
        let startNonterm = (List.Tot.hd (List.Tot.filter Helpers.isStartRule ruleList)).name.text in
        List.Tot.map (setStart startNonterm) (
            Helpers.unliftDepType isNonUnitRule (
                List.Tot.filter isNonUnitRule (
                    Helpers.removeDuplicates (
                        ruleList @ List.Tot.collect (newRules ruleList) (
                            findAllUnitPair ruleList)))))
