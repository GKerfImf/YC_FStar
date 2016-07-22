module Main
	open FStar.IO
	open IL
	open Yard.Core.Conversions

//----------------------------------------------------------------------------------------------------------------------------------------------------------

    val create: 
         production 'a 'b -> Tot (elem 'a 'b)
    let create arule = {omit=false; binding=None; checker=None; rule = arule}

	val testForDeleteChainRule: list (rule0: (rule source source) {Helpers.isPSeq rule0.body}) 
	let testForDeleteChainRule = (Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None); PToken (new_Source0 "s")]))
	    @ (Helpers.simpleNotStartRule "A" (List.Tot.map create [PRef (new_Source0 "B", None)]))
	    @ (Helpers.simpleNotStartRule "B" (List.Tot.map create [PRef (new_Source0 "C", None)]))
	    @ (Helpers.simpleNotStartRule "C" (List.Tot.map create [PToken (new_Source0 "c")]))
	    @ (Helpers.simpleNotStartRule "C" (List.Tot.map create [])) 

	val testForSplitLongRule: list (rule source source)
	let testForSplitLongRule = (Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None); PRef (new_Source0 "B", None); PRef (new_Source0 "C", None); PRef (new_Source0 "D", None); PToken (new_Source0 "s")]))
	    @ (Helpers.simpleNotStartRule "A" (List.Tot.map create [PRef (new_Source0 "A", None); PRef (new_Source0 "B", None); PRef (new_Source0 "C", None); PRef (new_Source0 "D", None); PToken (new_Source0 "a")]))
	    @ (Helpers.simpleNotStartRule "B" (List.Tot.map create [PRef (new_Source0 "A", None); PRef (new_Source0 "B", None); PRef (new_Source0 "C", None); PRef (new_Source0 "D", None); PToken (new_Source0 "b")]))
	    @ (Helpers.simpleNotStartRule "C" (List.Tot.map create [PRef (new_Source0 "A", None); PRef (new_Source0 "B", None); PRef (new_Source0 "C", None); PRef (new_Source0 "D", None); PToken (new_Source0 "c")]))
	    @ (Helpers.simpleNotStartRule "D" (List.Tot.map create [PRef (new_Source0 "A", None); PRef (new_Source0 "B", None); PRef (new_Source0 "C", None); PRef (new_Source0 "D", None); PToken (new_Source0 "d")])) 

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
		-> (list (rule0: (rule a b) {Helpers.isPSeq rule0.body} )) -> string
	let rec printListRule #a #b ruleList = 
		if (List.Tot.length ruleList > 1) 
		then printrule (List.Tot.hd ruleList) ^ "\n" ^  printListRule (List.Tot.tl ruleList)
		else (match ruleList with | [] -> "[]" | x::xs -> printrule x)

    let main =
        print_string "Hello, universes!\n";
		print_string ("\n" ^ printListRule testForSplitLongRule ^ "\n");
		print_string ("\n" ^ printListRule (SplitLongRule.splitLongRule testForSplitLongRule) ^ "\n")
		//
		//print_string ("\n" ^ printListRule (DeleteChainRule.deleteChainRule testForDeleteChainRule) ^ "\n")
		//
		//
		
