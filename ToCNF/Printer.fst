module Printer
	open FStar.IO
	open IL


	val flat_concat: list string -> Tot string
	let rec flat_concat l = match l with | [] -> "" | x::xs -> x ^ " " ^ flat_concat xs 

	val getText: production 'a 'b -> Tot string
    let getText = function 
    	| PToken(s) | PRef (s,_) -> s.text
        | _ -> ""

    //val printruleBody: production 'a 'b -> string
    let printruleBody1 = function 
        | PSeq (ruleSeq, _, _) -> ruleSeq |> List.Tot.map (fun x -> "" ^ getText x.rule ^ "")  |> flat_concat
        | _ -> ""

            
	let printrule rule =
        let st = if rule.isStart then "*" else "" in 
		st ^ rule.name.text ^ " --> " ^ printruleBody1 rule.body

//TODO: ???
    let printruleBody2 ruleSeq = ruleSeq |> List.Tot.map getText |> flat_concat



	let rec printListRule = function 
		| [] -> "" 
		| hd::tl -> printrule hd  ^ "\n" ^ printListRule tl

	let rec printListBody = function 
		| [] -> "" 
		| hd::tl -> printruleBody2 hd  ^ "\n" ^ printListBody tl