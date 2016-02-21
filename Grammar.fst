module Grammar
    open Rule

(*module -- Keyword*)
(*    
    type aModule 'patt 'expr =
    | Module : rules:(list (Rule.t 'patt 'expr)) -> openings:(list Source.t) -> name:(option Source.t) -> (allPublic:bool) -> aModule 'patt 'expr
    
    type t 'patt 'expr  = list (aModule 'patt 'expr) 
*)

    type aModule 'patt 'expr = {
        rules       : list (Rule.t 'patt 'expr);
        openings    : list Source.t;
        name        : option Source.t; 
        allPublic   : bool
    }

    type t 'patt 'expr  = list (aModule 'patt 'expr) 