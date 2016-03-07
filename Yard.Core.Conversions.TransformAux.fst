module Yard.Core.Conversions.TransformAux
    open IL
    open IL.MkModule
    
    (*let getText = Source.toString

    let rec getTextIL = function
        //| PRef(s,None) -> getText s
        | PRef(s,_) -> getText s
        | PToken(s) -> getText s
        | PLiteral(s) -> getText s
        | POpt(p) -> "(" + getTextIL p + ")?"
        | PSome(p) -> "(" + getTextIL p + ")*"
        | PMany(p) -> "(" + getTextIL p + ")+"
        | PAlt(l,r) -> "(" + getTextIL l + ")|(" + getTextIL r + ")"
        | PMetaRef(s,_,_) -> getText s
        | PSeq(elements, ac, _) ->
            "(" + (elements |> List.map (fun elem -> getTextIL elem.rule) |> String.concat " ") + "){" + 
            (match ac with Some(t) -> getText t | None -> "") + "}"
        | _ -> failwith "Unsupported meta param construct"

    *)

    let createSimpleElem rulProd bind = 
        { omit = false; rule = rulProd; binding = bind; checker = None }

    let createDefaultElem rulProd = createSimpleElem rulProd None


    let createRule name args body _public mArgs = 
        { 
            name = name; 
            args = args; 
            body = body; 
            isStart = _public; 
            metaArgs = mArgs; 
            isPublic = false            //Rule.
        }

    (*
    /// Non-start rule with empty meta-arguments list
    let createSimpleRule name args body =
        createRule name args body false []

    /// Replace first (name) field in Source.t with new source 
    let getNewSource (old : Source.t) n =
        new Source.t(n, old.startPos, old.endPos, old.file)

    //let createSource n = new Source.t(n)

    //let createRef ruleName _params = PRef (createSource ruleName, _params)

    let addBinding _params = function None -> _params | Some x -> x::_params

    /// Reduce param list to string. Arguments are separated by spaces
    let createParams = 
        function
        | []         -> []
        | [x]        -> e
        | (h ::hs)    -> let _params = String.concat " " (List.map getText (h ::hs)) 
                        in [getNewSource h _params]

    /// Create option from empty or one element list
    let list2opt = function
        | []     -> None
        | [h]    -> Some h (** list contains only one element!!! *)
        | _other -> invalidArg "list2opt" "Input list cannot contains more than one element." 

    let opt2list = function
        | None -> []
        | Some x -> [x]

    (* end of TransformAux *)

    *)