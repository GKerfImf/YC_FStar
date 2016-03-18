module Yard.Core.Conversions.TransformAux
    open IL

    val createSimpleElem: Production 'a 'b -> option 'a -> Tot (elem 'a 'b)
    let createSimpleElem rulProd bind = 
        { omit = false; rule = rulProd; binding = bind; checker = None }

    val createDefaultElem: Production 'a 'b -> Tot (elem 'a 'b)
    let createDefaultElem rulProd = createSimpleElem rulProd None

    val createRule: Source -> list 'a -> Production 'a 'b -> bool -> list 'a -> Tot (Rule 'a 'b)
    let createRule name args body _public mArgs = 
        { name = name; args = args; body = body; isStart = _public; metaArgs = mArgs; isPublic = false }
