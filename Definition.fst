(*--build-config
    options:--admit_fsi Set --admit_fsi Map;
    other-files:FStar.Set.fsi FStar.Heap.fst map.fsi
 --*)

(* https://github.com/FStarLang/FStar/blob/81e93898ad52579ea11368f869c1616e6cb7cbb1/ulib/FStar.TwoLevelHeap.fst *)

module Definition   
    open FStar.Map
    type info = fileName: string

    (*define comparison?*)
    type t 'patt'expr (*when 'patt : comparison and 'expr : comparison*) = { 
     info       : info;
     head       : option 'expr;
     grammar    : Grammar.t 'patt 'expr;
     foot       : option 'expr;
     (*options    : Map string string;                   --> Identifier not found: [Map] *)
     (*tokens     : Map string (option string);          --> Identifier not found: [Map] *)
    }    
    
    (* Empty Grammar *)
    let empty = { 
        info = "";                  (* {fileName = ""} *)
        head = None; 
        foot = None; 
        grammar = []; 
        (* options = Map.empty; *) 
        (* tokens = Map.empty   *)
    }