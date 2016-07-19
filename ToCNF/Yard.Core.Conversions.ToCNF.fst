module Yard.Core.Conversions.ToCNF
    open IL
    open Yard.Core.Conversions
    
//--CNF--------------------------------------------------------------------------------------------------------
    val toCNFrule: list (Rule 'a 'b) -> Tot (list (Rule 'a 'b))
    let toCNFrule ruleList =
        RenameTerm.renameTerm (
            DeleteUseless.deleteUseless (
                DeleteChainRule.deleteChainRule (
                 DeleteEpsRule.deleteEpsRule(
                        SplitLongRule.splitLongRule (
                            ruleList))))) 
