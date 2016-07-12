module Yard.Core.Conversions.DeleteChainRule
    open IL

    val getTextPRef: prod: Production 'a 'b {Helpers.isPRef prod} -> Tot string
    let getTextPRef prod = match prod with PRef(t,_) -> t.text

    val isUnitRule: rule: Rule 'a 'b {Helpers.isPSeq rule.body} -> Tot bool
    let isUnitRule rule = match rule.body with PSeq(elements,_,_) -> List.length elements = 1 && Helpers.isPRef (List.Tot.hd elements).rule

    val isNonUnitRule: rule: Rule 'a 'b {Helpers.isPSeq rule.body} -> Tot bool
    let isNonUnitRule rule = not (isUnitRule rule)

//***** getChain ****************************************************************************************************************************

//  Должно быть как-то так:

//    val filterLengthLemma: f:('a -> Tot bool) -> l:(list 'a) -> 
//        Lemma 
//            (requires True) 
//            (ensures (List.length (List.Tot.filter f l)) <= List.length l) 
//            [SMTPat (List.Tot.filter f l)]
//    let rec filterLengthLemma f l =
//        match l with
//        | [] -> ()
//        | hd::tl -> filterLengthLemma f tl

//    val except: list string -> original:list string -> Tot (filtered:list string {List.length filtered <= List.length original}) 
//    let except itemsToExclude lst = 
//        List.Tot.filter (fun el -> not (List.Tot.contains el itemsToExclude)) lst

//  assume val exceptLemma0: someList:(list string) -> exclList:(list string) -> -> 
//        Lemma 
//            (requires (True)) 
//            (ensures (forall (genList: list string). List.length (except (List.Tot.append someList exclList) genList) < List.length (except exclList genList))) 
//            [SMTPat (List.Tot.append someList exclList)]

//    assume val exceptLemma1: exclList:(list string) -> genList:(list string) -> 
//      Lemma 
//          (requires True) 
//          (ensures (List.length (except exclList genList) = List.length (except (removeDuplicates exclList) genList)))
//          [SMTPat (removeDuplicates exclList)]

//  val getChain: 
//      chain: list string 
//      -> unitPairs: list (string * string) 
//      -> Tot (list string) (decreases %[List.length (except chain (List.Tot.map snd unitPairs))])
//  let rec getChain chain unitPairs =
//  
//      let temp1 = List.Tot.map snd (List.Tot.filter (fun x -> (List.Tot.contains (fst x) chain)) unitPairs) in
//  
//      let sndUnPairs = List.Tot.map snd unitPairs in
//   
//      let newChain = removeDuplicates (List.Tot.append chain temp1) in
//       
//      if List.length (except newChain (List.Tot.map snd unitPairs)) = List.length (except chain (List.Tot.map snd unitPairs)) then chain
//      else getChain newChain unitPairs
//*******************************************************************************************************************************************


    val getChainHepler: sat:nat -> chain: list string -> unitPairs: list (string * string) -> Tot (list string) (decreases %[sat])
    let rec getChainHepler sat chain unitPairs =
        let newChain = Helpers.removeDuplicates (chain @ (List.Tot.map snd (List.Tot.filter (fun x -> (List.Tot.contains (fst x) chain)) unitPairs))) in
        if newChain <> chain && sat > 0 then getChainHepler (sat - 1) newChain unitPairs else chain

    val getChain: chain: list string -> unitPairs: list (string * string) -> Tot (list string)
    let getChain chain unitPairs = getChainHepler (List.Tot.length unitPairs) chain unitPairs

    val splitUnitRule: rule: (Rule 'a 'b) {Helpers.isPSeq rule.body && isUnitRule rule} -> Tot (string * string)
    let splitUnitRule rule = 
        let rightPart = match rule.body with PSeq(elems,_,_) -> getTextPRef (List.Tot.hd elems).rule in
        (rule.name.text, rightPart)


    val filter: f:('a -> Tot bool) -> list 'a -> Tot (list (m:'a {f m}))
    let rec filter f = function
        | [] -> []
        | hd::tl -> if f hd then hd::filter f tl else filter f tl

    
    val findAllUnitPair: list (rule: (Rule 'a 'b) {Helpers.isPSeq rule.body}) -> Tot (list (string * list string))
    let findAllUnitPair ruleList =
        let unitRules = filter isUnitRule ruleList in
        let unitPairs = List.Tot.map splitUnitRule unitRules in
        let leftParts = Helpers.removeDuplicates (List.Tot.map fst unitPairs) in
        List.Tot.map (fun x -> (x, getChain (List.Tot.map snd (List.Tot.filter (fun y -> fst y = x) unitPairs)) unitPairs)) leftParts


    val renameRule: string -> rule:(Rule 'a 'b){Helpers.isPSeq rule.body && isNonUnitRule rule} -> Tot (rule:(Rule 'a 'b){Helpers.isPSeq rule.body})
    let renameRule fstUnitPair rule = {rule with name = new_Source0 fstUnitPair}


    val newRules: list (rule: (Rule 'a 'b) {Helpers.isPSeq rule.body}) -> string * (list string) -> Tot (list (rule: (Rule 'a 'b) {Helpers.isPSeq rule.body}))
    let newRules ruleList unitPair =
        let nonUnitRules = filter isNonUnitRule ruleList in
        let isRuleNameEq x rule = rule.name.text = x in                                 //(Warning): Losing precision when encoding a function literal
        let rulesWithName x = List.Tot.filter (isRuleNameEq x) nonUnitRules in
        let tempRules = List.Tot.collect rulesWithName (snd unitPair) in 
        List.Tot.map (renameRule (fst unitPair)) tempRules


    val deleteChainRule: list (rule: (Rule 'a 'b) {Helpers.isPSeq rule.body}) -> Tot (list (rule: (Rule 'a 'b) {Helpers.isPSeq rule.body && isNonUnitRule rule}))
    let deleteChainRule ruleList = 
        filter isNonUnitRule (Helpers.removeDuplicates (ruleList @ List.Tot.collect (newRules ruleList) (findAllUnitPair ruleList)))
