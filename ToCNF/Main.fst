module Main
	open FStar.IO
	open IL
	open Yard.Core.Conversions

//----------------------------------------------------------------------------------------------------------------------------------------------------------

    val create: 
         production 'a 'b -> Tot (elem 'a 'b)
    let create arule = {omit=false; binding=None; checker=None; rule = arule}


	val testForSplitLongRule: list ( rule0: (rule source source) {Helpers.isPSeq rule0.body} )
	let testForSplitLongRule = (Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None); PRef (new_Source0 "B", None)]))
	    @ (Helpers.simpleNotStartRule "A" (List.Tot.map create [PToken (new_Source0 "a"); PRef (new_Source0 "B", None); PToken (new_Source0 "c"); PRef (new_Source0 "D", None);]))
	    @ (Helpers.simpleNotStartRule "B" (List.Tot.map create [PToken (new_Source0 "d");PToken (new_Source0 "e");PToken (new_Source0 "f")]))

	val testForDeleteEpsRule: list ( rule0: (rule source source) {Helpers.isPSeq rule0.body} )
	let testForDeleteEpsRule = (Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None); PRef (new_Source0 "B", None)]))
	    @ (Helpers.simpleNotStartRule "A" (List.Tot.map create [PToken (new_Source0 "a")]))
	    @ (Helpers.simpleNotStartRule "A" (List.Tot.map create []))
	    @ (Helpers.simpleNotStartRule "B" (List.Tot.map create [PToken (new_Source0 "a")]))

	val testForDeleteChainRule: list (rule0: (rule source source) {Helpers.isPSeq rule0.body}) 
	let testForDeleteChainRule = (Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None)]))
	    @ (Helpers.simpleNotStartRule "A" (List.Tot.map create [PRef (new_Source0 "B", None)]))
	    @ (Helpers.simpleNotStartRule "B" (List.Tot.map create [PRef (new_Source0 "C", None)]))
	    @ (Helpers.simpleNotStartRule "C" (List.Tot.map create [PToken (new_Source0 "c")]))
	    @ (Helpers.simpleNotStartRule "C" (List.Tot.map create [])) 
//----------------------------------------------------------------------------------------------------------------------------------------------------------

	let rec concat l = match l with | [] -> "" | x::xs -> x ^ " " ^ concat xs 

	let printrule rule =
        let printruleBody2 ruleBody = 
            match ruleBody with
            | PToken(s) |PRef (s,_) -> s.text
            | _ -> "" in 

        let printruleBody ruleBody = 
            match ruleBody with
            | PSeq (ruleSeq, _, _) -> ruleSeq |> List.Tot.map (fun x -> "(" ^ printruleBody2 x.rule ^ ")")  |> concat
            | PToken(s) |PRef (s,_) -> s.text
            | _ -> "" in 

		(if rule.isStart then "*" else "") ^ rule.name.text ^ " --> " ^ printruleBody rule.body


	val printListRule: #a:eqtype-> #b:eqtype
		-> (list (rule0: (rule a b))) -> string
	let rec printListRule #a #b ruleList = 
		if (List.Tot.length ruleList > 1) 
		then printrule (List.Tot.hd ruleList) ^ "\n" ^  printListRule (List.Tot.tl ruleList)
		else (match ruleList with | [] -> "[]" | x::xs -> printrule x)

	val printListRule2: #a:eqtype-> #b:eqtype
		-> (list (rule0: (rule a b) )) -> string
	let rec printListRule2 #a #b ruleList = 
		if (List.Tot.length ruleList > 1) 
		then printrule (List.Tot.hd ruleList) ^ "\n" ^  printListRule2 (List.Tot.tl ruleList)
		else (match ruleList with | [] -> "[]" | x::xs -> printrule x)

	val id: #a:Type-> #b:Type
		-> rule0: (rule a b)-> Tot (rule a b)
	let id #a #b rule = rule


	val lforget: #a:Type-> #b:Type
		-> list (rule0: (rule a b) {Helpers.isPSeq rule0.body}) -> Tot (list (rule a b))
	let lforget #a #b l = List.Tot.map id l

	val lforget2: #a:Type-> #b:Type
		-> list (rule0: (rule a b) {Helpers.isPSeq rule0.body /\ DeleteChainRule.isNonUnitRule rule0}) -> Tot (list (rule a b))
	let lforget2 #a #b l = List.Tot.map id l

    let main =
        print_string "Hello, universes!\n";
		print_string ("\n" ^ printListRule2 (lforget testForDeleteChainRule) ^ "\n");
		//print_string ("\n" ^ printListRule2 (SplitLongRule.splitLongRule testForSplitLongRule) ^ "\n")
		//print_string ("\n" ^ printListRule2 (DeleteEpsRule.deleteEpsRule testForDeleteEpsRule) ^ "\n")
		print_string ("\n" ^ printListRule (lforget2 (DeleteChainRule.deleteChainRule testForDeleteChainRule)) ^ "\n")
