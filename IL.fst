module IL
	open FStar.Set
	open FStar.Heap

// Old module Source
//-----------------------------------------------------------------------------------------------------------------
	type Position = {
		absoluteOffset : ref int;
		line: ref int;
		column : ref int
		//toString : unit -> string
	}

	let new_position a l c = 
		let a = ref a in
		let l = ref l in
		let c = ref c in
			{absoluteOffset = a; line = l; column = c}

	(* temp *)
	type Lexing_Position = {
		absoluteOffset : ref int; 
		line : ref int; 
		column : ref int
	}

	(* not "new_position" :( *)
	let new_position2 (fslexPos : Lexing_Position) =
			{absoluteOffset = fslexPos.absoluteOffset; line = fslexPos.line; column = fslexPos.column} 

	type Source = {
		text : ref string;
		startPos : ref Position;
		endPos : ref Position;
		file : ref string
	}

	let new_Source t s e f = 
		let t = ref t in
		let s = ref s in
		let e = ref e in
		let f = ref f in
			{text = t; startPos = s; endPos = e; file = f}

	(* (new_position 0 0 0) -- new Position()  :( *)
	let new_Source0 text = new_Source text (new_position 0 0 0) (new_position 0 0 0) ""

(*		new (text, origin : Sourse) =
            {text = text; startPos = origin.startPos; endPos = origin.endPos; file = origin.file}
        new (text, startPos : Lexing.Position, endPos : Lexing.Position) =
            Sourse (text, new Position(startPos), new Position(endPos), startPos.FileName)
        new (text, lexbuf : Lexing.LexBuffer<_>) =
            Sourse (text, lexbuf.StartPos, lexbuf.EndPos) *)
//-----------------------------------------------------------------------------------------------------------------


// Old module Production
//-----------------------------------------------------------------------------------------------------------------
    (*  let num = ref 0                                                                                 *) 
    (*  type IRuleType = interface end                       (????)                                     *)
        
    type DLabel = {
        label: string;
        weight: option float
    }
 
    type elem 'patt 'expr = {
        (*  Don't include rule into AST                                                                 *)
        omit:bool;
        (*  Production rule itself.                                                                     *)
        rule:(Production 'patt 'expr);
        (*  Binding :) like f:F or f:=F.... Seal                                                        *)
        binding:option 'patt;
        (*  Almost resolver (condition in production).                                                  *)
        checker:option 'expr
    }
    (*  <summary>                                                                                       *)
    (*  <para>t&lt;'patt,'expr&gt; - Type of production node in derivation tree. </para>                *)
    (*  <para>  'patt - type of l-attributes. </para>                                                   *)
    (*  <para>  'expr - type of expressions in action code. </para>                                     *)
    (*  </summary>                                                                                      *)
	and Production 'patt 'expr = 
        (*  Alternative (e1 | e2)                                                                       *)
        | PAlt     of (Production 'patt 'expr) * (Production 'patt 'expr)
        (*  Sequence * attribute. (Attribute is always applied to sequence)                             *)
        | PSeq     of list (elem 'patt 'expr)  * option 'expr * option DLabel
        (*  Token itself. Final element of parsing.                                                     *)
        | PToken   of Source
        (*  Reference to other rule inside production. With an optional args list.                      *)
        | PRef     of Source * option 'expr 
        (*  expr*                                                                                       *)
        | PMany    of (Production 'patt 'expr)
        (*  Reference to metarule inside production (mr<<x>> in rule "a: mr<<x>> y z")                  *)
        | PMetaRef of Source * (option 'expr) * list (Production 'patt 'expr) 
        (*  Literal. We can use constants ("if" and "then" in ' .."if" expr "then" expr...')            *)
        | PLiteral of Source 
        (*  Extended regexp repetition, "man egrep" for details                                         *)
        | PRepet   of (Production 'patt 'expr ) * (option int) * (option int) 
        (*  Permutation (A || B || C)                                                                   *)
        | PPerm    of list (Production 'patt 'expr) 
        (*  The following are obsolete and reduction to PRepet should be discussed.                     *)
        (*  expr+                                                                                       *)
        | PSome    of (Production 'patt 'expr)
        (*  expr?                                                                                       *)
        | POpt     of (Production 'patt 'expr)  

        (* with 																						*)
        (* override this.ToString() = 																	*)
//-----------------------------------------------------------------------------------------------------------------


// Old module Rule
//-----------------------------------------------------------------------------------------------------------------
    (*  <summary>                                                                                       *)
    (*  <para>t&lt;'patt,'expr&gt; - Type of rule. </para>                                              *)
    (*  <para>  'patt - type of attributes (arguments). </para>                                         *)
    (*  <para>  'expr - type of expressions in action code. </para>                                     *)
    (*  <para>Rule have the following format: </para>                                                   *)
    (*  <para>  [+]name&lt;&lt; metaArgs &gt;&gt;[args] : body; </para>                                 *)
    (*  </summary>                                                                                      *)
    type Rule 'patt 'expr = {
        (*  Rule name. Used to start from this or to be referenced to from other rules.                 *)
        name    : Source;
        (*  Heritable arguments of rule                                                                 *)
        args    : list 'patt;
        (*  Rule body (production).                                                                     *)
        body    : Production 'patt 'expr;
        (*  Is this rule a start non-terminal (in this case '[<Start>]' is used before rule)            *)
        isStart : bool;
        (*  Can this rule be seen from another module.                                                  *)
        (*  It's true if ('public' is used before rule) or (module is marked as AllPublic and rule isn't marked as private)*)
        isPublic : bool;
        (*  List of meta-arguments - names of rules, parametrizing this rule.                           *)
        metaArgs: list 'patt
    }

    let defaultRule name body = {
        name = name; 
        body = body; 
        args = []; 
        isStart = false; 
        isPublic = false; 
        metaArgs = []
    }
//-----------------------------------------------------------------------------------------------------------------


// Old module Grammar
//-----------------------------------------------------------------------------------------------------------------
    type Module 'patt 'expr = {
        (*  Module is a list of rules                                                                   *)
        rules : list (Rule 'patt'expr);
        openings : list Source;
        name : option Source;
        (*  Are all rules public (can be seen form another module), except explicitly marked as private.*)
        (*  Otherwise rule must be directly marked as public to be seen.                                *)
        allPublic : bool
    }
    (*  Grammar is a list of modules                                                                    *)
    type Grammar 'patt 'expr = list (Module 'patt 'expr)
//-----------------------------------------------------------------------------------------------------------------


// Old module Definition
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
        options : Map string string;
        tokens : Map string (option string)
    }    
    
    (*  Empty grammar                                                                                       *)
    let empty = { 
        info = {fileName = ""}; 
        head = None; 
        foot = None; 
        grammar = []; 
        options = Map.empty; 
        tokens = Map.empty
    }