module Yard.Core.Conversions.Helpers
    open IL

    val isPToken: production 'a 'b -> Tot bool
    let isPToken #a #b = function
        | PToken(_) -> true 
        | _ -> false

    val isPRef: production 'a 'b -> Tot bool
    let isPRef #a #b = function
        | PRef(_) -> true 
        | _ -> false

    val isPSeq: production 'a 'b -> Tot bool
    let isPSeq #a #b = function
        | PSeq(_) -> true 
        | _ -> false


    val isEpsRule: #a:Type -> #b:Type
        -> rule a b -> Tot bool
    let isEpsRule #a #b rule0 = match rule0.body with 
        | PSeq([], _, _) -> true 
        | _ -> false

    val isStartRule: #a:Type -> #b:Type
        -> rule a b -> Tot bool
    let isStartRule #a #b rule = rule.isStart

    val isPTokenRule: #a:Type -> #b:Type
        -> rule0: (rule a b) {isPSeq rule0.body} -> Tot bool
    let isPTokenRule #a #b rule0 = match rule0.body with 
        | PSeq(elements,_,_) -> 
            List.Tot.length elements = 1 
            && (let hd_el: (elem a b) = List.Tot.hd elements in
                let hd_rule:(production a b) = hd_el.rule in 
                isPToken hd_rule)


    val getLeftPart: #a:Type -> #b:Type
        -> rule a b -> Tot string
    let getLeftPart #a #b rule = rule.name.text

    val getRightPartList: #a:Type -> #b:Type
        -> rule0: rule a b {isPSeq rule0.body} -> Tot (list string)
    let getRightPartList #a #b rule = match rule.body with | PSeq(elements,_,_) -> 
            List.Tot.collect (fun elem -> match elem.rule with | PRef(s,_) | PToken(s) -> [s.text] | _ -> []) elements

    val getRightPartPRefList: #a:Type -> #b:Type
        -> rule0: rule a b {isPSeq rule0.body} -> Tot (list string)
    let getRightPartPRefList #a #b rule = match rule.body with | PSeq(elements,_,_) -> 
            List.Tot.collect (fun elem -> match elem.rule with | PRef(s,_) -> [s.text] | _ -> []) elements


//TODO: {isPSeq rule.body}  ------------------------------------------------
    val getPSeqBodyLength: #a:Type -> #b:Type 
        -> production a b -> Tot nat
    let getPSeqBodyLength #a #b prod = List.Tot.length (match prod with | PSeq(e, a, l) -> e | _ -> [])

    val getRightPartLength: #a:Type -> #b:Type
        -> rule a b -> Tot nat
    let getRightPartLength #a #b rule = getPSeqBodyLength rule.body
//------------------------------------------------


    val simpleRule: #a:Type -> #b:Type
        -> string -> list (elem a b) -> bool -> Tot (rule0: (rule a b) {Helpers.isPSeq rule0.body})
    let simpleRule #a #b nonTerm seq b =
        {name = new_Source0 nonTerm; args = []; body = PSeq(seq, None, None); isStart = b; isPublic = false; metaArgs = []}

    val simpleStartRule: #a:Type -> #b:Type
        -> string -> list (elem a b) -> Tot ( (rule0: (rule a b) {Helpers.isPSeq rule0.body}))
    let simpleStartRule #a #b nonTerm seq = simpleRule nonTerm seq true

    val simpleNotStartRule: #a:Type -> #b:Type
        -> string -> list (elem a b) -> Tot ( (rule0: (rule a b) {Helpers.isPSeq rule0.body}))
    let simpleNotStartRule #a #b nonTerm seq = simpleRule nonTerm seq false
    
//------------------------------------------------

    // (List.filter f list).length <= list.length
    val filterLengthLemma: #a:eqtype -> f:(a -> Tot bool) -> l:(list a) -> 
        Lemma 
            (requires True) 
            (ensures (List.Tot.length (List.Tot.filter f l)) <= List.Tot.length l) 
            [SMTPat (List.Tot.filter f l)]
    let rec filterLengthLemma #a f l = 
        match l with  
        | [] -> ()
        | hd::tl -> filterLengthLemma f tl

    val except: list string -> original:list string -> Tot (filtered:list string {List.Tot.length filtered <= List.Tot.length original}) 
    let except itemsToExclude lst = 
        List.Tot.filter (fun el -> not (List.Tot.contains el itemsToExclude)) lst

    val removeDuplicates: #a:eqtype -> list a -> Tot (list a)
    let removeDuplicates #a lst = 
        let helpRemDup item acc = match acc with 
            | [] -> [item]
            | _ -> if List.Tot.existsb (fun x -> x = item) acc then acc else item::acc in 
        List.Tot.fold_right helpRemDup lst []



    private val filter: #a:Type -> f:(a -> Tot bool) -> list a -> Tot (list (m: a{f m}))
    let rec filter #a f l = match l with 
        | [] -> []
        | hd::tl -> if f hd then hd::filter f tl else filter f tl

    val unliftDepType: #a:eqtype -> f:(a -> Tot bool) -> xs: list a {forall x. List.Tot.mem x xs ==> f x} -> Tot (list (x: a {f x}))
    let unliftDepType #a f xs = filter f xs


    //TODO:
    //val liftDepType: #a:eqtype -> f:(a -> Tot bool) -> list (x: a {f x}) -> Tot (xs: list a {forall x. List.Tot.mem x xs ==> f x})


    //Example
    //val forget: a:Type -> b:Type -> p:(a->Type) -> q:(a->Type) -> r:(x:a{p x} * y:b{q y}) -> Tot (s: (a*b){fst s = fst r && snd s = snd r})


//--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    val forget: a:eqtype -> p:(a -> Tot bool) -> x: a {p x} -> Tot a
    let forget a p x = x
   
    val lift:
        #a:eqtype -> #p:(a -> Tot bool)
        -> list (x: a {p x})
        -> Tot (l: (list a) {forall x. List.Tot.mem x l ==> p x} )                            
    let lift #a #p lst = List.Tot.filter p (List.Tot.map (forget a p) lst)
       
    val unlift:
        #a:eqtype -> p:(a -> Tot bool)
        -> l: (list a) {forall x. List.Tot.mem x l ==> p x}          
        -> Tot (list (x: a {p x}))                          
    let unlift #a p lst = filter p lst  

   
(*
fail:
    // map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
    // (map f): list 'a -> Tot (list 'b)
    //
    // > f: (n: nat {p1 n} -> Tot bool)
    // (map f): list (n: nat {p1 n}) -> Tot (list bool)
    // lift (map f): l:list nat {forall n. List.Tot.mem n l ==> p1 n} -> Tot (list bool)
 
    val liftF:
        #a:eqtype -> #b:eqtype -> #p:(a -> Tot bool)
        -> m: ( ('c -> Tot 'd) -> list 'c -> Tot (list 'd) )
        -> f:(x: a {p x} -> Tot b)
        -> l: (list a) {forall x. List.Tot.mem x l ==> p x}
        -> Tot (list b)                                                  
    let liftF #a #b #c #d #p m f l = m (f) (unlift p l)
 
 
     val liftF:
        #a:eqtype -> #b:eqtype -> #p:(a -> Tot bool) -> #q:(a -> Tot bool)
        -> m: ( (a -> Tot b) -> list a -> Tot (list b) )
        -> f:( x: a {p x} -> Tot (y: b {q y}) )
        -> l1: (list a) {forall x. List.Tot.mem x l1 ==> p x}
        -> Tot ( l2: (list a) {forall y. List.Tot.mem y l2 ==> q y} )    
 
 
    val liftF:
        #a:eqtype -> #p:(a -> Tot bool) -> #q:(a -> Tot bool)
        -> m: ( f:(x:a{p x} -> Tot (y:b{q y})) -> list (x:a{p x}) -> Tot (list (y:b{q y})) )
        -> l1: (list a) {forall x. List.Tot.mem x l1 ==> p x}
        -> Tot ( l2: (list a) {forall y. List.Tot.mem y l2 ==> q y} )                            
    let liftF #a #p lst = List.Tot.filter p (List.Tot.map (id a p) lst)
*)
   
    
 
    assume val p1: n:nat -> Tot bool
    assume val p2: n:nat -> Tot bool
   

    assume val f: n: nat {p1 n} -> Tot bool

    assume val fl1: list (n: nat {p1 n}) -> Tot bool
    assume val fl2: l:list nat {forall n. List.Tot.mem n l ==> p1 n} -> Tot bool
 
 
(*
    val liftF:
        #a:eqtype -> #p:(a -> Tot bool)
        -> f:( list (x: a {p x}) -> Tot bool )
        -> Tot (l: (list a) {forall x. List.Tot.mem x l ==> p x} -> Tot bool)
    let liftF #a #p f = fun x -> f (unlift p x)    
   
       
    val test4:
        ln1: list nat {forall n. List.Tot.mem n ln1 ==> p1 n}
        -> ln2: list nat {forall n. List.Tot.mem n ln2 ==> (p1 n /\ p2 n)}
        -> Tot bool                                  
    let test4 ln1 ln2 = (liftF fl1) ln1 || (liftF fl1) ln2
*)
 
   
    val liftF1:
        a:eqtype -> b:eqtype -> p:(a -> Tot bool) -> q:(b -> Tot bool)
        -> f:(list (x: a {p x}) -> Tot (list (y: b {q y})))
        -> Tot (l1: (list a) {forall x. List.Tot.mem x l1 ==> p x} -> Tot (l2: (list b) {forall y. List.Tot.mem y l2 ==> q y}))
    let liftF1 a b p q f =  fun x -> lift (f (unlift p x))  


    val liftF2:
        a:eqtype -> b:eqtype -> p:(a -> Tot bool) -> q:(b -> Tot bool)
        -> f:(list (x: a {p x}) -> Tot (list (y: b {q y})))
        -> Tot (l1: (list a) {forall x. List.Tot.mem x l1 ==> p x} -> Tot (list (y: b {q y}))) //Tot (l2: (list b) {forall y. List.Tot.mem y l2 ==> q y}))
    let liftF2 a b p q f =  fun x -> f (unlift p x)

 
    val liftF3:
        #a:eqtype -> #p:(a -> Tot bool)
        -> f:(list (x: a {p x}) -> Tot (list bool))
        -> Tot (l1: (list a) {forall x. List.Tot.mem x l1 ==> p x} -> Tot (l2: (list bool)))
    let liftF3 #a #p f =  liftF1 a bool p (fun x -> true) f  
   
   
   
   
//TODO: 
//    val test2:
//        ln1: list (n: nat {p1 n})
//        -> ln2: list (n: nat {p1 n && p2 n})
//        -> Tot bool
//    let test2 ln1 ln2 = fl1 ln1 || fl1 (Keeek.lift ln2)    //fail 
   
   
 
    val test6:
        ln1: list nat {forall n. List.Tot.mem n ln1 ==> p1 n}
        -> ln2: list nat {forall n. List.Tot.mem n ln2 ==> p1 n && p2 n}
        -> Tot (list bool)
    let test6 ln1 ln2 =  
        liftF3 (List.Tot.map f) ln1 @ liftF3 (List.Tot.map f) ln2
     
     
     
                                                             
    //assume val s: a:Type -> b:(Type -> Type) -> b a
   
   
    //let t = s (n: int {n > 0}) (list)


//-------------------- Equ ------------------------------------------------------------------------------------------

    val getProds: #a:eqtype -> #b:eqtype -> rule a b -> Tot (list (production a b))
    let getProds #a #b rule = match rule.body with
        | PSeq(els,_,_) -> List.Tot.map (fun elem -> elem.rule) els
        | _ -> []

    val left: #a:eqtype -> #b:eqtype -> rule a b -> Tot (production a b)
    let left #a #b rule = PRef (rule.name, None) 

    val rigth: #a:eqtype -> #b:eqtype -> r: rule a b -> Tot (list (production a b))
    let rigth #a #b rule = getProds rule 

//-------------------------------------------------------------------------------------------------------------------