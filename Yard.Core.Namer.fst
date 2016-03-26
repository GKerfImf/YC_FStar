module Yard.Core.Namer
    open IL
    open String

    val prodNewName: int -> string -> Tot string
    let prodNewName n str = str ^ (string_of_int n)

(*    val prodNewNameLemma:  
        n:int -> str:string -> 
        Lemma
            (requires ( True )) 
            (ensures ( str <> (prodNewName n str) ))
    let rec prodNewNameLemma n str =
        match n, str with
        | 0, "0" -> ()  //Он даже это не может сам 
        | _,_ -> admit()
*)

(*    val prodNewNameLemma:  
        n:int -> str:string -> 
        Lemma
            (requires ( True )) 
            (ensures ( str <> (prodNewName n str) ))
    let rec prodNewNameLemma n str =
        let str2 = prodNewName n str in 
        match str with
        | "" -> ()              //И так не работает
        | _ -> admit()
*)

(*  И так не работает
    val prodNewNameLemma:  
        n:int -> str:string -> 
        Lemma
            (requires ( True )) 
            (ensures ( [str] <> (prodNewName n str) ))
            [SMTPat (prodNewName n str)]
    let prodNewNameLemma n str = ()
    
    val injStringConcat:  
        strLst1: list string -> strLst2: list string -> 
        Lemma
            (requires ( strLst1 <> strLst2 /\ )) 
            (ensures ( (String.concat "" strLst1) <> (String.concat "" strLst2) ))
            //[SMTPat (String.concat "" strLst1)]
    let rec injStringConcat s1 s2 =
        match s1,s2 with
        | [],[] -> ()
        | [],hd::tl -> (if h="" then injStringConcat [] t else ())
        | _,[] -> admit()
        | hd1::tl1, hd2::tl2 -> admit()
        |_,_ -> admit()
    
    val prodNewNameLemma2:  
        n:int -> str:string -> 
        Lemma
            (requires ( True )) 
            (ensures (String.concat "" [str] <> String.concat "" (prodNewName n str) ))
    let prodNewNameLemma2 n str = ()
*)

    val newSource: n:int -> oldSource:Source -> Tot Source 
    let newSource n old = 
        ({ old with text = prodNewName n old.text})


    assume val newSourceLemma:  
        n:int -> source:Source ->  
        Lemma (source <> newSource n source)

    assume val injectiveNewSource: 
        source1:Source -> source2:Source ->
        Lemma   (requires (source1 <> source2))
                (ensures (forall n m. (newSource n source1 <> newSource m source2)))
