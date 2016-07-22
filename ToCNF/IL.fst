module IL

type position = {
    absoluteOffset : int;
    line: int;
    column : int	
}
assume HasEq_position: hasEq position

let new_position a l c = {absoluteOffset = a; line = l; column = c}

type source = {
    text : string;
    startPos : position;
    endPos : position;
    file : string
}
assume HasEq_source: hasEq source

let new_Source t s e f = {text = t; startPos = s; endPos = e; file = f}
	
let new_Source0 text = new_Source text (new_position 0 0 0) (new_position 0 0 0) ""

type dLabel = {
    label: string;
    weight: option int//float
}
assume HasEq_dLabel: hasEq dLabel
 
type elem 'patt 'expr = {
    //Don't include rule into AST                                                                 
    omit:bool;
    //Production rule itself.                                                                     
    rule:(production 'patt 'expr);
    //Binding :) like f:F or f:=F.... Seal                                                        
    binding:option 'patt;
    //Almost resolver (condition in production).                                                  
    checker:option 'expr
}

//'patt,'expr; - Type of production node in derivation tree.
//'patt - type of l-attributes.
//  'expr - type of expressions in action code.
and production 'patt 'expr = 
    (*  Alternative (e1 | e2)                                                                       *)
    (*| PAlt     of (production 'patt 'expr) * (production 'patt 'expr)                             *)
    (*  Sequence * attribute. (Attribute is always applied to sequence)                             *)
    | PSeq     of list (elem 'patt 'expr)  * option 'expr * option dLabel
    (*  Token itself. Final element of parsing.                                                     *)
    | PToken   of source
    (*  Reference to other rule inside production. With an optional args list.                      *)
    | PRef     of source * option 'expr 
    (*  expr*                                                                                       *)
    (*| PMany    of (production 'patt 'expr)                                                        *)
    (*  Reference to metarule inside production (mr<<x>> in rule "a: mr<<x>> y z")                  *)
    (*| PMetaRef of source * (option 'expr) * list (production 'patt 'expr)                         *)
    (*  Literal. We can use constants ("if" and "then" in ' .."if" expr "then" expr...')            *)
    (*| PLiteral of source                                                                          *)
    (*  Extended regexp repetition, "man egrep" for details                                         *)
    (*| PRepet   of (production 'patt 'expr ) * (option int) * (option int)                         *)
    (*  Permutation (A || B || C)                                                                   *)
    (*| PPerm    of list (production 'patt 'expr)                                                   *)
    (*  The following are obsolete and reduction to PRepet should be discussed.                     *)
    (*  expr+                                                                                       *)
    (*| PSome    of (production 'patt 'expr)                                                        *)
    (*  expr?                                                                                       *)
    (* | POpt     of (production 'patt 'expr)                                                       *)

assume HasEq_elem: forall a b. hasEq a /\ hasEq b ==> hasEq (elem a b)
assume HasEq_production: forall a b. hasEq a /\ hasEq b ==> hasEq (production a b)



type rule 'patt 'expr = {
    (*  Rule name. Used to start from this or to be referenced to from other rules.                 *)
    name    : source;
    (*  Heritable arguments of rule                                                                 *)
    args    : list 'patt;
    (*  Rule body (Production).                                                                     *)
    body    : production 'patt 'expr;
    (*  Is this rule a start non-terminal (in this case '[<Start>]' is used before rule)            *)
    isStart : bool;
    (*  Can this rule be seen from another module.                                                  *)
    (*  It's true if ('public' is used before rule) or (module is marked as AllPublic and rule isn't marked as private)*)
    isPublic : bool;
    (*  List of meta-arguments - names of rules, parametrizing this rule.                           *)
    metaArgs: list 'patt
}
assume HasEq_rule: forall a b. hasEq a /\ hasEq b ==> hasEq (rule a b)

let defaultRule name body = {
    name = name; 
    body = body; 
    args = []; 
    isStart = false; 
    isPublic = false; 
    metaArgs = []
}

(*
// Grammar
//-----------------------------------------------------------------------------------------------------------------
    type module 'patt 'expr = {
        (*  Module is a list of rules                                                                   *)
        rules : list (Rule 'patt 'expr);
        openings : list Source;
        name2 : option Source;              //name
        (*  Are all rules public (can be seen form another module), except explicitly marked as private.*)
        (*  Otherwise rule must be directly marked as public to be seen.                                *)
        allPublic : bool
    }
    (*  Grammar is a list of modules                                                                    *)
    type grammar 'patt 'expr = list (module 'patt 'expr)
//-----------------------------------------------------------------------------------------------------------------


// Definition
//-----------------------------------------------------------------------------------------------------------------
    type info = { fileName: string }

    type Definition 'patt 'expr (*when 'patt : comparison and 'expr : comparison> *) = { 
        (*  Contains information (e.g. origin) about this grammar description                               *)
        info    : info;
        (*  Text before a grammar description ( e.g. some open-s), what will be simply copied               *)
        head    :option 'expr ;
        (*  Grammar description itself                                                                      *)
        grammar : Grammar 'patt 'expr;
        (*  Text after a grammar description, what will be simply copied                                    *)
        foot    : option 'expr;
        (*options : Map string string;*)
        (*tokens : Map string (option string)*)
    }    
    
    (*  Empty grammar                                                                                       *)
    let empty = { 
        info = {fileName = ""}; 
        head = None; 
        foot = None; 
        grammar = []; 
        (*options = Map.empty; *)
        (*tokens = Map.empty*)
    }
*)
