module Main
	open FStar.IO
	open IL
	//open Equ
	open Yard.Core.Conversions


//TODO: move to Helpers 
    val create: 
         production 'a 'b -> Tot (elem 'a 'b)
    let create arule = {omit=false; binding=None; checker=None; rule = arule}



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

//TODO: assume val isWellFormed: list (rule 'a 'b) -> Tot ( list ( rule0: (rule source source) {Helpers.isPSeq rule0.body} ) )

    let main =
        print_string "Hello, universes!\n\n" ;

        //print_string (EquAlt.main ^ "\n")

		//print_string ("\n" ^ Printer.printListRule (Helpers.lift testForDeleteChainRule) ^ "\n")
		//print_string ("\n" ^ printListRule2 (SplitLongRule.splitLongRule testForSplitLongRule) ^ "\n")

		print_string ("\n" ^ Printer.printListRule (Helpers.lift testForDeleteEpsRule) ^ "\n");
		print_string ("\n" ^ Printer.printListRule (DeleteEpsRule.deleteEpsRule testForDeleteEpsRule) ^ "\n")
		//print_string ("\n" ^ printListRule (Helpers.lift (DeleteChainRule.deleteChainRule testForDeleteChainRule)) ^ "\n")
