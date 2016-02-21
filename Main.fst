module Main
	#set-options "--initial_ifuel 1 --max_ifuel 1"
	open FStar.IO
	open FStar.Util
	open FStar.HyperHeap
	open Source
    

(*	https://github.com/FStarLang/FStar/
		blob/6cb40de54a68a1fd226dba02946c942e86700a8f/old/to_be_ported/monadic/JSBuiltIns-monadic_old.fst 
*)
	val tToString: Source.t -> Tot string
    let tToString (x : Source.t) = (T.text x) ^ " " ^ (T.file x)

(*	//let print_message x = print_string x
;;
   
//print_message "fuck this\n"
//print_message (tToString h ^ "\n") 
*)