module Production
    open Source

(*  let num = ref 0
    type IRuleType = interface end *)
        
    type dLabel = 
        | DLabel : label:string -> (weight: option float) -> dLabel
 
(*  type dLabel = {
        label:string;
        weight: option float
    } *)
    
    
	type elem 'patt 'expr = 
		| Elem : omit:bool -> rule:(t 'patt 'expr) -> binding:option 'patt -> checker:option 'expr -> elem 'patt 'expr

	and t 'patt 'expr = 
        (*  Alternative (e1 | e2)                                                                       *)
        | PAlt     of (t 'patt 'expr) * (t 'patt 'expr)
        (*  Sequence * attribute. (Attribute is always applied to sequence)                             *)
        | PSeq     of list (elem 'patt 'expr)  * option 'expr * option dLabel
        (*  Token itself. Final element of parsing.                                                     *)
        | PToken   of Source.t 
        (*  Reference to other rule inside production. With an optional args list.                      *)
        | PRef     of Source.t * option 'expr 
        (*  expr*                                                                                       *)
        | PMany    of (t 'patt 'expr)
        (*  Reference to metarule inside production (mr<<x>> in rule "a: mr<<x>> y z")                  *)
        | PMetaRef of Source.t * (option 'expr) * list (t 'patt 'expr) 
        (*  Literal. We can use constants ("if" and "then" in ' .."if" expr "then" expr...')            *)
        | PLiteral of Source.t 
        (*  Extended regexp repetition, "man egrep" for details                                         *)
        | PRepet   of (t 'patt 'expr ) * (option int) * (option int) 
        (*  Permutation (A || B || C)                                                                   *)
        | PPerm    of list (t 'patt 'expr) 
        (*  The following are obsolete and reduction to PRepet should be discussed.                     *)
        (*  expr+                                                                                       *)
        | PSome    of (t 'patt 'expr)
        (*  expr?                                                                                       *)
        | POpt     of (t 'patt 'expr)  