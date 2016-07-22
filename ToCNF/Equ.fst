module Equ
	open FStar.IO
	open IL
	open Yard.Core.Conversions

	//let isTerm = Helpers.isPToken
	//let isNon

	type sentence (patt:eqtype) (expr:eqtype) = terms: list (production patt expr){forall prod. List.Tot.mem prod terms ==> Helpers.isPToken prod}
	type sententialForm (patt:Type) (expr:Type) = list (production patt expr)



	val isSentence: #a:eqtype -> #b:eqtype -> list (production a b) -> Tot bool
	let isSentence #a #b prodList = 
		List.Tot.for_all Helpers.isPToken prodList

	val str: list (production source source)
	let str = [PRef (new_Source0 "A", None); PToken (new_Source0 "s")]


	val wordE: sentence source source
	let wordE = [PToken (new_Source0 "1"); PToken (new_Source0 "2")]


	//val lderive: #a:Type -> #b:Type -> ruleList: list (rule a b) -> list (production a b) -> int//list (production a b) 
	//let lderive #a #b ruleList str =
	//	0

	//val bind: list 'a -> ('a -> Tot (list 'b)) -> Tot (list 'b)
	//let bind lst f =  


	assume val lderives: #a:Type -> #b:Type -> (ruleList: list (rule a b)) -> (oldSF: sententialForm a b) -> (newSF: sententialForm a b) -> Tot bool
	assume val getStartNonterm: #a:Type -> #b:Type -> list (rule a b) -> Tot (sententialForm a b)




	type language (a:eqtype) (b:eqtype) (ruleList: list (rule a b)) = 
		lang: list (sentence a b) {forall sent. List.Tot.mem sent lang ==> lderives ruleList (getStartNonterm ruleList) sent}

	assume val transformation: #a:eqtype -> #b:eqtype
		-> list (rule a b) -> Tot (list (rule a b))

    assume val lemma0: 
    	#a:eqtype -> #b:eqtype
		-> ruleList: list (rule a b) -> l1: language a b ruleList -> l2: language a b (transformation ruleList)
        -> Lemma 
            (requires True) 
            (ensures (forall x. List.Tot.mem x l1 ==> List.Tot.mem x l2)) 

    assume val lemma1: 
    	#a:eqtype -> #b:eqtype
		-> ruleList: list (rule a b) -> l1: language a b ruleList -> l2: language a b (transformation ruleList)
        -> Lemma 
            (requires True) 
            (ensures (forall x. List.Tot.mem x l2 ==> List.Tot.mem x l1)) 

		





    let main = 
    	//assert (isSentence wordE);
    	//assert (isSentence str);

    	0


 	
//	val test: list (rule0: (rule source source) {Helpers.isPSeq rule0.body}) 
//	let test = (Helpers.simpleStartRule "S" (List.Tot.map create [PRef (new_Source0 "A", None); PToken (new_Source0 "s")]))
//	    @ (Helpers.simpleNotStartRule "A" (List.Tot.map create [PRef (new_Source0 "B", None)]))
//	    @ (Helpers.simpleNotStartRule "B" (List.Tot.map create [PRef (new_Source0 "C", None)]))
//	    @ (Helpers.simpleNotStartRule "C" (List.Tot.map create [PToken (new_Source0 "c")]))
//	    @ (Helpers.simpleNotStartRule "C" (List.Tot.map create [])) 

	//nlist?? = list non_terminal

