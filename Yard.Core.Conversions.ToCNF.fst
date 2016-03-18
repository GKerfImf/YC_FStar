module Yard.Core.Conversions.ToCNF
    open IL
    open Yard.Core.Conversions
    
//--CNF--------------------------------------------------------------------------------------------------------
    let toCNFrule (ruleList: list (Rule _ _)) = 
        ruleList
        |> SplitLongRule.splitLongRule
        |> DeleteEpsRule.deleteEpsRule 
        |> DeleteChainRule.deleteChainRule
        |> RenameTerm.renameTerm 


//-- Main lemma sketch

assume val grammar_eq : g1:Grammar 'a 'b -> g2:Grammar 'a 'b -> Tot bool

assume val isCFG:  g:Grammar 'a 'b -> Tot bool
assume val isCNF:  g:Grammar 'a 'b -> Tot bool
assume val toCNF:  g:Grammar 'a 'b -> Tot (Grammar 'a 'b)

assume val main_lemma: 
	g: Grammar 'a 'b -> 
		Lemma 
			(requires (isCFG g)) 
			(ensures ( isCNF (toCNF g) /\ grammar_eq (toCNF g) (g) ))
