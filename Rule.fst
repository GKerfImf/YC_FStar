module Rule
    (* <summary>
    /// <para>t&lt;'patt,'expr&gt; - Type of rule. </para>
    /// <para>  'patt - type of attributes (arguments). </para>
    /// <para>  'expr - type of expressions in action code. </para>
    /// <para>Rule have the following format: </para>
    /// <para>  [+]name&lt;&lt; metaArgs &gt;&gt;[args] : body; </para>
    /// </summary> *)

(*  type t 'patt 'expr =
    | T : 
        (* Rule name. Used to start from this or to be referenced to from other rules.                                      *)
        name    : Source.t ->
        (* Heritable arguments of rule                                                                                      *)
        args    : list 'patt ->
        (* Rule body (production).                                                                                          *)
        body    : (Production.t 'patt 'expr) ->
        (* Is this rule a start non-terminal (in this case '[<Start>]' is used before rule)                                 *)
        isStart : bool ->
        (* Can this rule be seen from another module.                                                                       *)
        (* It's true if ('public' is used before rule) or (module is marked as AllPublic and rule isn't marked as private)  *)
        isPublic : bool ->
        (* List of meta-arguments - names of rules, parametrizing this rule.                                                *)
        metaArgs: list 'patt -> 
                                        t 'patt 'expr*)

    type t 'patt 'expr = {                                    
        name    : Source.t;
        args    : list 'patt;
        body    : (Production.t 'patt 'expr);
        isStart : bool;
        isPublic : bool;
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
