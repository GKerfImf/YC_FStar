module Main
open FStar.IO
open IL
open Yard.Core.Conversions
open Yard.Core.Conversions.DeleteChainRule

//----------------------------------------------------------------------------------------------------------------------------------------------------------

val create: Production 'a 'b -> Tot (elem 'a 'b)
let create aRule = {omit=false; binding=None; checker=None; rule = aRule}

let test = (Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None); PToken (new_Source0 "s")]))
    @ (Helpers.simpleNotStartRule "A" (List.map create [PRef (new_Source0 "B", None)]))
    @ (Helpers.simpleNotStartRule "B" (List.map create [PRef (new_Source0 "C", None)]))
    @ (Helpers.simpleNotStartRule "C" (List.map create [PToken (new_Source0 "c")]))
    @ (Helpers.simpleNotStartRule "C" (List.map create [])) 
//----------------------------------------------------------------------------------------------------------------------------------------------------------

let rec concat l = match l with [] -> "" | x::xs -> x ^ " " ^ concat xs 

let printRule rule =
	let rec printRuleBody ruleBody = 
	    match ruleBody with
        | PSeq (ruleSeq, _, _) -> ruleSeq |> List.map (fun x -> "(" ^ printRuleBody x.rule ^ ")")  |> concat
        | PToken(s) |PRef (s,_) -> s.text
        | _ -> "" in 

	(if rule.isStart then "*" else "") ^ rule.name.text ^ " --> " ^ printRuleBody rule.body


val printListRule1: (list (rule: (Rule 'a 'b) {Helpers.isPSeq rule.body} )) -> string
let rec printListRule1 ruleList = 
	if (List.length ruleList > 1) 
	then printRule (List.hd ruleList) ^ "\n" ^  printListRule1 (List.tl ruleList)
	else printRule (List.hd ruleList)

val printListRule2: (list (rule: (Rule 'a 'b) {Helpers.isPSeq rule.body && isNonUnitRule rule})) -> string
let rec printListRule2 ruleList = 
	if (List.length ruleList > 1) 
	then printRule (List.hd ruleList) ^ "\n" ^  printListRule2 (List.tl ruleList)
	else printRule (List.hd ruleList)



let main =
	print_string ("\n" ^ printListRule1 test ^ "\n");
	print_string ("\n" ^ printListRule2 (deleteChainRule test) ^ "\n")



