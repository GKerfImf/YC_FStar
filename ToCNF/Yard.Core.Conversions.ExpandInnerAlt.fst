module Yard.Core.Conversions.ExpandInnerAlt
	//open Yard.Core
	//open TransformAux
	//open Mono.Addins
	open IL

	let dummyPos s = new_Source0 s

	let expandInnerAlts (ruleList: list (Rule _ _)) = 
		(* F#: let toExpand = new System.Collections.Generic.Queue<Rule.t<_,_>>(List.toArray ruleList) *)
		//let expanded = 
		0

(* 

let private expandInnerAlts (ruleList: Rule.t<_,_> list) = 
	--
    let expanded = ref []
    while toExpand.Count > 0 do
        let toExpandRule = toExpand.Dequeue()
        let rec expandBody attrs = function
            | PSeq(elements, actionCode, l) -> 
                elements |> List.fold (fun (res, attrs) elem ->
                    match elem.rule with 
                    | PSeq(subelements, None, l) when subelements.Length = 1 -> 
                        { elem with rule = (List.head subelements).rule }
                    | PSeq(subelements, subActionCode, l) when subelements.Length > 1 || subActionCode <> None ->
                        let newName = Namer.newName Namer.Names.brackets
                        toExpand.Enqueue({name = dummyPos newName; args=attrs; body=elem.rule;
                                            isStart=false; isPublic=false; metaArgs=[]})
                        { elem with rule = PRef(dummyPos newName, list2opt <| createParams attrs) }
                    | PAlt(_,_) -> 
                        let newName = Namer.newName Namer.Names.brackets
                        toExpand.Enqueue({name = dummyPos newName; args=attrs; body=elem.rule;
                                            isStart=false; isPublic=false; metaArgs=[]})
                        { elem with rule = PRef(dummyPos newName, list2opt <| createParams attrs) }
                    | _ -> elem
                    |> fun newElem -> newElem::res, if elem.binding.IsSome then attrs@[elem.binding.Value] else attrs
                ) ([], attrs)
                |> fst |> List.rev
                |> fun elems -> PSeq (elems, actionCode, l)
            | PAlt(left, right) -> PAlt(expandBody attrs left, expandBody attrs right)
            | x -> x
        
        let expandedRule = expandBody toExpandRule.args toExpandRule.body
        expanded := { toExpandRule with body=expandedRule } :: !expanded
        ()
    List.rev !expanded


[<assembly:Addin>]
[<assembly:AddinDependency ("YaccConstructor", "1.0")>]
do()

[<Extension>]
type ExpandInnerAlt() = 
    inherit Conversion()
        override this.Name = "ExpandInnerAlt"
        override this.ConvertGrammar (grammar,_) = mapGrammar expandInnerAlts grammar
*)