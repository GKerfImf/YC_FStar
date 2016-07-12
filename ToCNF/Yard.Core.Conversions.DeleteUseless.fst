module Yard.Core.Conversions.DeleteUseless
    open IL

    val getGenHelper: nat -> list string -> list (Rule 'a 'b) -> Tot (list string) 
    let rec getGenHelper len acc ruleList = 
        let newAcc = 
            Helpers.removeDuplicates (
                List.Tot.append acc (
                    List.Tot.map Helpers.getLeftPart (
                        List.Tot.filter (fun rule -> List.Tot.for_all (fun x -> List.Tot.contains x acc) (Helpers.getRightPartPRefList rule)) (
                            ruleList)))) in

        if newAcc <> acc && len > 0 then getGenHelper (len - 1) newAcc ruleList 
        else acc 

    val getGen: list string -> list (Rule 'a 'b) -> Tot (list string) 
    let getGen acc ruleList = getGenHelper (List.length ruleList) acc ruleList 

    val deleteNongeneratingNonterminals: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
    let deleteNongeneratingNonterminals ruleList =
        let isWeakGen rule = (Helpers.isEpsRule rule) || (Helpers.isPTokenRule rule) in

        let temp = 
            Helpers.removeDuplicates (
                List.Tot.map Helpers.getLeftPart (
                    List.Tot.filter isWeakGen (
                        ruleList))) in

        let gen = getGen temp ruleList in

        List.Tot.filter (fun rule -> List.Tot.for_all (fun y -> List.Tot.contains y gen) (Helpers.getRightPartPRefList rule)) ruleList



    val getReachableHelper: nat -> list string -> list (Rule 'a 'b) -> Tot (list string)
    let rec getReachableHelper len acc ruleList = 
        let newAcc = 
            Helpers.removeDuplicates (
                List.Tot.append acc (
                    List.Tot.collect Helpers.getRightPartPRefList (
                        List.Tot.filter (fun rule -> List.Tot.contains (Helpers.getLeftPart rule) acc) (
                            ruleList)))) in

        if newAcc <> acc && len > 0 then getReachableHelper (len - 1) newAcc ruleList
        else acc

    val getReachable: list string -> list (Rule 'a 'b) -> Tot (list string)
    let getReachable acc ruleList =
        let temp1 =  List.Tot.collect Helpers.getRightPartPRefList ruleList in
        let temp2 =  List.Tot.map Helpers.getLeftPart ruleList in
        let maxLen = List.Tot.length (temp1 @ temp2) in
        getReachableHelper maxLen acc ruleList 

    val deleteUnreachableNonterminals: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
    let deleteUnreachableNonterminals ruleList =
        let startRules = 
            Helpers.removeDuplicates (
                List.Tot.map Helpers.getLeftPart (
                    List.Tot.filter (fun rule -> rule.isStart) (
                        ruleList))) in
        let reachable = getReachable startRules ruleList in
         List.Tot.filter (fun rule -> List.Tot.contains (Helpers.getLeftPart rule) reachable) ruleList
        
        
    val deleteUseless: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))        
    let deleteUseless ruleList = 
        deleteUnreachableNonterminals (deleteNongeneratingNonterminals (ruleList)) 

       