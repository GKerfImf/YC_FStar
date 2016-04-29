module Yard.Core.Conversions.TransformAux
    open IL

    val createSimpleElem: Production 'a 'b -> option 'a -> Tot (elem 'a 'b)
    let createSimpleElem rulProd bind = 
        { omit = false; rule = rulProd; binding = bind; checker = None }

    val createDefaultElem: Production 'a 'b -> Tot (elem 'a 'b)
    let createDefaultElem rulProd = createSimpleElem rulProd None


    val lengthBodyRule: Rule 'a 'b -> Tot int
    let lengthBodyRule rule = List.length (match rule.body with PSeq(e, a, l) -> e | _ -> [])

    val createRule: 
    	Source 
    	-> list 'a 
    	-> body:(Production 'a 'b){ (fun body -> (List.length (match body with PSeq(e, a, l) -> e | _ -> []) <= 2 )) body} 
    	-> bool 
    	-> list 'a 
    	-> Tot (rule:(Rule 'a 'b){lengthBodyRule rule <= 2})
    let createRule name args body _public mArgs = 
        { name = name; args = args; body = body; isStart = _public; metaArgs = mArgs; isPublic = false }


(* 
    val lengthBody: Production 'a 'b -> Tot int
    let lengthBody production = List.length (match production with PSeq(e, a, l) -> e | _ -> [])

    val lengthBodyRule: Rule 'a 'b -> Tot int
    let lengthBodyRule rule = List.length (match rule.body with PSeq(e, a, l) -> e | _ -> [])

    val createRule: 
    	Source 
    	-> list 'a 
    	-> body:(Production 'a 'b){ lengthBody body <= 2} 
    	-> bool 
    	-> list 'a 
    	-> Tot (rule:(Rule 'a 'b){lengthBodyRule rule <= 2})
    let createRule name args body _public mArgs = 
        { name = name; args = args; body = body; isStart = _public; metaArgs = mArgs; isPublic = false }
*)