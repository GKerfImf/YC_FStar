module Main
    open FStar.IO
    open IL
    open Yard.Core.Conversions


//TODO: move to Helpers 
    val create: production 'a 'b -> Tot (elem 'a 'b)
    let create a_rule = {omit=false; binding=None; checker=None; rule = a_rule}

    val testForDeleteStartSymbol: list ( rule0: (rule source source) {Helpers.isPSeq rule0.body} )
    let testForDeleteStartSymbol = [Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "S", None); PRef (new_Source0 "S", None)]);
        Helpers.simpleStartRule "S" (List.Tot.map create [PToken (new_Source0 "a"); PRef (new_Source0 "B", None)]);
        Helpers.simpleNotStartRule "B" (List.Tot.map create [PToken (new_Source0 "a")])]

    val testForSplitLongRule: list ( rule0: (rule source source) {Helpers.isPSeq rule0.body} )
    let testForSplitLongRule = [Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None); PRef (new_Source0 "B", None)]);
        Helpers.simpleNotStartRule "A" (List.Tot.map create [PToken (new_Source0 "a"); PRef (new_Source0 "B", None); PToken (new_Source0 "c"); PRef (new_Source0 "D", None)]);
        Helpers.simpleNotStartRule "B" (List.Tot.map create [PToken (new_Source0 "d");PToken (new_Source0 "e");PToken (new_Source0 "f")])]

    val testForDeleteEpsRule: list ( rule0: (rule source source) {Helpers.isPSeq rule0.body} )
    let testForDeleteEpsRule = [Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None); PRef (new_Source0 "B", None)]);
        Helpers.simpleNotStartRule "A" (List.Tot.map create [PToken (new_Source0 "a")]);
        Helpers.simpleNotStartRule "A" (List.Tot.map create []);
        Helpers.simpleNotStartRule "B" (List.Tot.map create [PToken (new_Source0 "a")])]

    val testForDeleteChainRule: list (rule0: (rule source source) {Helpers.isPSeq rule0.body}) 
    let testForDeleteChainRule = [Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None)]);
        Helpers.simpleNotStartRule "A" (List.Tot.map create [PRef (new_Source0 "B", None)]);
        Helpers.simpleNotStartRule "B" (List.Tot.map create [PRef (new_Source0 "C", None)]);
        Helpers.simpleNotStartRule "C" (List.Tot.map create [PToken (new_Source0 "c")]);
        Helpers.simpleNotStartRule "C" (List.Tot.map create [])]

    //val testForDeleteUseless: list (rule0: (rule source source) {Helpers.isPSeq rule0.body}) 
    //val testForRenameTerm: list (rule0: (rule source source) {Helpers.isPSeq rule0.body}) 


//TODO: assume val isWellFormed: list (rule 'a 'b) -> Tot ( list ( rule0: (rule source source) {Helpers.isPSeq rule0.body} ) )

    let main =
        print_string "Hello, universes!\n\n" ;

        print_string ("\n" ^ Printer.printListRule (Helpers.lift testForDeleteStartSymbol) ^ "\n");
        //print_string ("\n" ^ Printer.printListRule (Helpers.lift (DeleteStartSymbol.deleteStartSymbol testForDeleteStartSymbol)) ^ "\n");

        print_string ""


(* check
    deleteEpsRule:

    *S --> S S 
    *S --> a B 
    B --> a 

        ==>

    *S --> S 
    *S --> S 
    *S --> S S 
    *S --> a B 
    B --> a
*)