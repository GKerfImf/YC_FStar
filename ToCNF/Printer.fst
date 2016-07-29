module Printer
	open FStar.IO
	open IL
	open Yard.Core.Conversions




	private let rec concat l = match l with | [] -> "" | x::xs -> x ^ " " ^ concat xs 


    private let getText = function 
    	| PToken(s) | PRef (s,_) -> s.text
        | _ -> ""


	private let printrule rule =

        let printruleBody = function 
            | PSeq (ruleSeq, _, _) -> ruleSeq |> List.Tot.map (fun x -> "" ^ getText x.rule ^ "")  |> concat
            | _ -> "" in 

        let st = if rule.isStart then "*" else "" in 

		st ^ rule.name.text ^ " --> " ^ printruleBody rule.body



//TODO: ???
    private let printruleBody ruleSeq = ruleSeq |> List.Tot.map getText |> concat



	let rec printListRule = function 
		| [] -> "" 
		| hd::tl -> printrule hd  ^ "\n" ^ printListRule tl

	let rec printListBody = function 
		| [] -> "" 
		| hd::tl -> printruleBody hd  ^ "\n" ^ printListBody tl