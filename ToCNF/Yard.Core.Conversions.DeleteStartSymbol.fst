module Yard.Core.Conversions.DeleteStartSymbol
    open IL

    //TODO: cfg = {ss, rules} ???


	//TODO: del
    //val create: production 'a 'b -> Tot (elem 'a 'b)
    //let create a_rule = {omit=false; binding=None; checker=None; rule = a_rule}
    


    val deleteStartSymbol: #a:eqtype -> #b:eqtype 
        -> list (rule0: rule a b {Helpers.isPSeq rule0.body}) 
        -> Tot (list (rule0: rule a b {Helpers.isPSeq rule0.body}))
    let deleteStartSymbol #a #b ruleList =
    	//let create = Helpers.simpleStartRule "S" ({omit=false; binding=None; checker=None; rule = [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]}) in 
    	ruleList