Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import List.
Import ListNotations.
Open Scope list_scope.


Inductive nt: Type :=
  NT : string -> nt.

Inductive t: Type :=
  T : string -> t.

Definition sf: Type := list (sum nt t).
Definition rule: Type := (nt * sf).

Record cfg: Type:= {
  start_symbol: nt;
  rules: (list rule);
}.

Definition terminal_lift (s: t): nt + t := inr s.

Inductive derives (g: cfg): sf -> sf -> Prop :=
| derives_refl: forall (s: sf),
                derives g s s
| derives_step: forall (s1 s2 s3: sf) (left: nt) (right: sf),
                derives g s1 (s2 ++ inl left :: s3) ->
                In (left,right) (rules g) ->
                derives g s1 (s2 ++ right ++ s3).

Theorem derives_trans (g: cfg) (s1 s2 s3: sf):
derives g s1 s2 ->
derives g s2 s3 ->
derives g s1 s3.
Proof.
intros H1 H2.
induction H2. 
- exact H1.
- apply derives_step with (left:=left).
  + apply IHderives.
    exact H1.
  + exact H.
Qed.


Definition generates (g: cfg) (s: list (nt + t)): Prop:=
  derives g [inl (start_symbol g)] s.

Definition produces (g: cfg) (s: list t): Prop:=
  generates g (map terminal_lift s).


Definition g_equiv (g1: cfg) (g2: cfg): Prop:=
  forall s: list t, produces g1 s <-> produces g2 s.

Definition isSingle (rule: nt * sf) :=
  match rule with
  | (_,[inr _]) => true
  | _ => false
  end.


Definition getNewText (elem: t): string :=
  match elem with
  | T s => "New_" ++ s
  end.

Definition renameElem (elem: nt + t) : ((nt + t) * (list (nt *sf))) :=
  match elem with
  | inr t => ( inl (NT ( getNewText t ) ) , [ ( NT ( getNewText t ), [ elem ] ) ] )
  | inl _ => ( elem, [] )
  end.


Definition renameRule (rule: nt * sf) : ( list (nt * sf) ) :=
  let res := map renameElem (snd rule) in
	match rule with
	| (l,r) => (l, map fst res):: flat_map snd res
  end.

Definition normalizeRule (rule: nt * sf) : ( list (nt * sf) ) :=
  if isSingle rule then [rule] else renameRule rule.

(* ---------------------------------------------------------------------------------- *)

Example example_1:
  forall left nt0,
  renameRule (left,[inl nt0]) = [(left,[inl nt0])].
Proof.
  intros. unfold renameRule. simpl. reflexivity. Qed.

Example example_2:
  forall left,
  renameRule (left,[]) = [(left,[])].
Proof.
  intros. unfold renameRule. simpl. reflexivity. Qed.

Example example_3:
  forall rule,
  isSingle rule = true ->
  normalizeRule rule = [rule].
Proof.
  intros. unfold normalizeRule. destruct isSingle. reflexivity. inversion H. Qed.

Example example_4:
  forall left t0,
  normalizeRule (left,[inr t0]) = [(left,[inr t0])].
Proof.  intros. reflexivity. Qed.

(* ---------------------------------------------------------------------------------- *)

Lemma concat_in_lemma:
  forall (A: Type) (x: A) (l1: list A) (l2: list A),
  In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros. induction l1.
  - simpl. split.
    + intros. right. assumption.
    + intros. destruct H. inversion H. assumption.
  - simpl. split.
    + intros. destruct H.
      * left. left. assumption.
      *  apply IHl1 in H. destruct H. left. right. assumption. right. assumption.
    + intros. destruct H. 
      * destruct H. left. assumption. right. apply IHl1. left. assumption.
      * right. apply IHl1. right. assumption.
Qed.

Lemma flat_map_lemma_1:
  forall (A:Type) (f: A -> list A) (x:A) (xs: list A),
    f x = [x] ->
    In x xs ->
    In x (flat_map f xs).
Proof.
  intros. induction xs.
    + inversion H0.
    + simpl. apply concat_in_lemma. assert (a :: xs = [a] ++ xs). simpl. reflexivity. rewrite H1 in H0.
      apply concat_in_lemma in H0.
      destruct H0.
      * inversion H0. subst. left. rewrite H. assumption. simpl. inversion H2.
      * right. apply IHxs. assumption.
Qed.

Lemma flat_map_lemma_2:
  forall (A:Type) (f: A -> list A) (x:A) (xs: list A),
    f x = [x] ->
    (forall x', In x (f x') -> x = x') ->
    In x (flat_map f xs) ->
    In x xs.
Proof.
  intros. induction xs.
  - inversion H1.
  - simpl in H1. apply concat_in_lemma in H1. destruct H1.
    + apply H0 in H1. subst. simpl. left. reflexivity.
    + simpl. right. apply IHxs. assumption.
Qed.

Lemma flat_map_lemma_3:
  forall (A B: Type) (f: A -> list B) (x: A) (y: B) (xs: list A),
    In x xs -> In y (f x) -> In y (flat_map f xs).
Proof.
  intros. induction xs.
  - inversion H.
  - simpl. destruct H.
    + apply concat_in_lemma. left. subst. assumption.
    + apply concat_in_lemma. right. apply IHxs. apply H. 
Qed.

Lemma arrow_disj_lemma: forall (A B C: Prop),
  ((A \/ B) -> C) ->
  (A -> C) /\ (B -> C).
Proof. intros. split; auto. Qed.

(* ---------------------------------------------------------------------------------- *)

Lemma norm_eps_lemma:
  forall left,
  normalizeRule (left,[]) = [(left,[])].
Proof. intros. reflexivity. Qed.

Lemma norm_single_lemma:
  forall left single,
  normalizeRule (left,[single]) = [(left,[single])].
Proof.
  intros. destruct single. reflexivity. reflexivity. Qed.

Lemma norm_2nonterm_lemma:
  forall left n0 n1,
  normalizeRule (left, [inl n0; inl n1]) = [(left, [inl n0; inl n1])].
Proof. intros. reflexivity. Qed.





(* Lemma lemma_4:
  forall left right leftN rightN,
    In (leftN,rightN) (normalizeRule (left,right)) -> length right = length rightN \/ length rightN = 1.
Proof.
  intros. induction right.
  - inversion H. simpl in H0. inversion H0. left. reflexivity. inversion H0.
  - 
Admitted. *)



(* Lemma lemma_14:
  forall l1 r1 l2 r2,
    r2 <> [] ->
    In (l1, r1) (normalizeRule (l2,r2)) -> length r1 > 0.
Proof.
  intros.
  unfold normalizeRule in H0. destruct isSingle in H0. 
  - inversion H0. inversion H1. subst. destruct r1. admit (* [] <> [] *). simpl. admit (* S () > 0 *). inversion H1.
  - induction r2.
    + admit (* [] <> [] *).
    + apply IHr2.
      * destruct a.  admit.
      * admit.
Qed. *)

(* Definition f (n:nat) :=
  match n with 
  | 0 => [0]
  | n => [n; n + 1]
  end
.

Lemma lemma_5:
  forall n, In 0 (f n) -> 0 = n.
Proof.
  intros. destruct n.
    reflexivity.
    simpl in H. destruct H. auto. destruct H. inversion H. inversion H. Qed.
 *)
 
Lemma lemma_15:
  forall l r ,
    In (l, []) (renameRule (l, r)) -> r = [].
Proof.
  intros l r H.
  induction r. reflexivity.
    simpl in H. destruct H. admit. admit. Admitted.

Lemma test_46:
  forall l1 r1 l s r,
    In (l1,r1) (renameRule (l, s::r)) -> length r1 > 0.
Proof.
  intros.
    destruct r1.
      
    simpl. admit.



Admitted.


Lemma lemma_5:
  forall left rule,
    In (left, []) (normalizeRule rule) -> (left, []) = rule.
Proof.
  intros.
  unfold normalizeRule in H. destruct isSingle in H.
  - inversion H. auto. inversion H0.
  - destruct rule0 as (l,r). destruct r.
    + simpl in H. destruct H. auto. inversion H.
    + apply test_46 in H. inversion H. (* unfold renameRule in H. unfold renameRule in IHr. simpl in H. simpl in IHr.
      destruct H. inversion H.
      apply concat_in_lemma in H. destruct H. admit.
      apply arrow_disj_lemma in IHr. destruct IHr. apply H1 in H. 
      apply IHr in H.
    
    replace (a :: r) with ([a] ++ r) in H. apply concat_in_lemma in H. destruct a. simpl in H. destruct H. inversion H. unfold normalizeRule in IHr. destruct isSingle in IHr. inversion H. *)
Qed.


Lemma lemma_6 :
  forall left nt0 x,
    In (left,[inl nt0]) (normalizeRule x) -> (left,[inl nt0]) = x.
Proof.
  intros. destruct x. (*  destruct s. *) induction s.
  - simpl in H. destruct H. auto. inversion H.
  - destruct a. simpl in H. destruct H. inversion H. inversion H3. simpl in IHs.
    + (* destruct a. simpl in H. destruct H. auto. inversion H. simpl in H. destruct H. inversion H. inversion H.
    + destruct a; destruct s.
      * simpl in H. destruct H. inversion H. simpl in IHs. apply IHs with in H. admit.
      * simpl in H. destruct H. inversion H. destruct H. inversion H. admit.
      * simpl in H. destruct H. inversion H. destruct H. inversion H. admit.
      * simpl in H. destruct H. inversion H. destruct H. inversion H. destruct H. inversion H. admit. *)
    auto.
Admitted.

Lemma lemma_7 :
  forall left t0 x,
    In (left,[inr t0]) (normalizeRule x) -> (left,[inr t0]) = x.
Proof.
  intros. destruct x. destruct s.
  - simpl in H. destruct H. auto. inversion H.
  - destruct s0.
    + destruct s. simpl in H. destruct H. auto. inversion H. simpl in H. destruct H. auto. inversion H.
    + assert (H' := H). (* apply lemma_4 in H. destruct H. inversion H. destruct s. simpl in H'.  admit. *)
Admitted.


(* Lemma lemma_8 :
  forall left n0 n1 x s0 s1,
   (*  (n0 <> NT ("New_" ++ s0)) -> (n1 <> NT ("New_" ++ s1)) -> *)
    In (left, [inl n0; inl n1]) (normalizeRule x) -> (left, [inl n0; inl n1]) = x. *)
Lemma lemma_8 :
  forall left x s0 s1,
   (*  (n0 <> NT ("New_" ++ s0)) -> (n1 <> NT ("New_" ++ s1)) -> *)
    In (left, [inl (NT ("_" ++ s0)); inl (NT ("_" ++ s1))]) (normalizeRule x) -> (left, [inl (NT ("_" ++ s0)); inl (NT ("_" ++ s1))]) = x.
Proof.
   intros left x ns0 ns1 H. destruct x. destruct s.
  - (* apply lemma_4 in H. destruct H. inversion H. inversion H.
  - destruct s0.
    + apply lemma_4 in H. destruct H. inversion H. inversion H.
    + destruct s1.
      * destruct s; destruct s0.
        -- simpl in H. destruct H. auto. inversion H.
        -- simpl in H. destruct H. inversion H. admit. admit.
        -- admit.
        -- admit.
      * apply lemma_4 in H. destruct H. inversion H. inversion H. *) Admitted.




Lemma test_47:
  forall left rules,
  In (left,[]) rules <-> In (left,[]) (flat_map normalizeRule rules).
Proof.
  intros. split.
  - apply flat_map_lemma_1. reflexivity.
  - apply flat_map_lemma_2. reflexivity. apply lemma_5. Qed.

Lemma test_52:
  forall left single rules,
  In (left, [single]) (flat_map normalizeRule rules) <-> In (left,[single]) rules.
Proof.
  intros. split.
  - apply flat_map_lemma_2.
    + apply norm_single_lemma.
    + admit.
  - apply flat_map_lemma_1. apply norm_single_lemma. Admitted.

Lemma test_53:
  forall left n0 n1 rules,
  In (left, [inl n0; inl n1]) (flat_map normalizeRule rules) <-> In (left, [inl n0; inl n1]) rules.
Proof.
  intros. split.
  - apply flat_map_lemma_2.
    + apply norm_2nonterm_lemma.
    + admit.
  - apply flat_map_lemma_1. apply norm_2nonterm_lemma. Admitted.


Definition renameTerms (g: cfg) := {|
  start_symbol := start_symbol g;
  rules := flat_map normalizeRule (rules g)
|}.


Definition short_rules (g: cfg) :=
  forall left right, 
    In (left, right) (rules g) -> length right <= 2.


Lemma custom_ass_1: forall (A:Type) (c1 c2: A) (s1 s2: list A), 
(s1 ++ [c1]) ++ [c2] ++ s2 = s1 ++ [c1; c2] ++ s2 .
Proof. intros. simpl. rewrite <- app_assoc with (l := s1) (m := [c1]) (n := c2 :: s2). reflexivity. Qed.

Lemma custom_ass_2: forall (A:Type) (c1 c2: A) (s1 s2: list A), 
s1 ++ [c1] ++ [c2] ++ s2 = (s1 ++ [c1; c2] ++ s2) .
Proof. intros. simpl. reflexivity. Qed.

Lemma custom_ass_3: forall (A:Type) (c1 c2: A) (s1 s2: list A),
(s1 ++ [c1]) ++ c2 :: s2 = s1 ++ [c1; c2] ++ s2.
Proof. intros. simpl. apply custom_ass_1. Qed.

Lemma Alg_prop_1:
  forall g left,
  In (left, []) (rules g) <->
  In (left, []) (rules (renameTerms g)).
Proof.
  split.
  - apply flat_map_lemma_1. apply norm_eps_lemma.
  - apply test_47. Qed.

Lemma Alg_prop_2:
  forall g left r_single,
  In (left, [r_single]) (rules g) <->
  In (left, [r_single]) (rules (renameTerms g)).
Proof.
  split.
  - apply flat_map_lemma_1. apply norm_single_lemma.
  - apply test_52. Qed.

Lemma Alg_prop_3:
  forall g left n0 n1,
  In (left, [inl n0; inl n1]) (rules g) <->
  In (left, [inl n0; inl n1]) (rules (renameTerms g)).
Proof.
  split.
  - apply flat_map_lemma_1. apply norm_2nonterm_lemma.
  - apply flat_map_lemma_2. apply norm_2nonterm_lemma. Admitted.

Lemma Alg_prop_4:
  forall g left n s0,
    In (left, [inl n; inr (T s0)]) (rules g) ->
    In (left, [inl n; inl (NT ("New_" ++ s0))]) (rules (renameTerms g)) /\ In (NT ("New_" ++ s0), [inr (T s0)]) (rules (renameTerms g)).
Proof.
  intros. split.
  - apply flat_map_lemma_3 with (x := (left, [inl n; inr (T s0)])). assumption. simpl. eauto.
  - apply flat_map_lemma_3 with (x := (left, [inl n; inr (T s0)])). assumption. simpl. eauto.
Qed.

Lemma Alg_prop_5:
  forall g left n s0,
    In (left, [inr (T s0); inl n]) (rules g) ->
    In (left, [inl (NT ("New_" ++ s0)); inl n]) (rules (renameTerms g)) /\ In (NT ("New_" ++ s0), [inr (T s0)]) (rules (renameTerms g)).
Proof.
  intros. split.
  - apply flat_map_lemma_3 with (x := (left, [inr (T s0); inl n])). assumption. simpl. eauto.
  - apply flat_map_lemma_3 with (x := (left, [inr (T s0); inl n])). assumption. simpl. eauto.
Qed.

Lemma Alg_prop_6:
  forall g left s0 s1,
  In (left, [inr (T s0); inr (T s1)]) (rules g) ->
  In (left, [inl (NT ("New_" ++ s0)); inl (NT ("New_" ++ s1))]) (rules (renameTerms g))
  /\ In (NT ("New_" ++ s0), [inr (T s0)]) (rules (renameTerms g))
  /\ In (NT ("New_" ++ s1), [inr (T s1)]) (rules (renameTerms g)).
Proof.
  intros. split;[|split].
  - apply flat_map_lemma_3 with (x := (left, [inr (T s0); inr (T s1)])). assumption. simpl. eauto.
  - apply flat_map_lemma_3 with (x := (left, [inr (T s0); inr (T s1)])). assumption. simpl. eauto.
  - apply flat_map_lemma_3 with (x := (left, [inr (T s0); inr (T s1)])). assumption. simpl. eauto.
Qed.


Lemma lemma_10:
  forall left n0 t0,
    ~ In (left, [inl n0; inr t0]) (normalizeRule (left, [inl n0; inr t0])).
Proof.
  intros left n0 t0 H.
  simpl in H. destruct H.
  - inversion H.
  - destruct H.
    + inversion H.
    + assumption.
Qed.


Definition isNonterm (el: nt + t) :=
  match el with
  | inl _ => True
  | inr _ => False
  end.
  
(* if isSingle rule0
       then [rule0]
       else renameRule rule0 *)

Lemma lemma_16:
  forall rule l r,
    In (l,r) (normalizeRule rule) ->
      (forall el, In el r -> isNonterm el) \/ (length r = 1).
Proof.
  intros.
    (* unfold normalizeRule in H. *) destruct rule0. induction s.
    - simpl in H. destruct H. inversion H. subst. left. intros. inversion H0. inversion H.
    - destruct a. 
      + simpl in H. destruct H.
        * inversion H. admit.
        * admit.
      + simpl in H.   simpl. 
       unfold normalizeRule in H. destruct isSingle in H.    left. intros. unfold isNonterm. admit.
  right.





Lemma lemma_11:
  forall rule left n0 t0,
    ~ In (left, [inl n0; inr t0]) (normalizeRule rule).
Proof.
  intros rule left n0 t0 H. destruct rule as (l,r).
  destruct r.
  - inversion H. simpl in H0. inversion H0. simpl in H0. assumption.
  - destruct s.
    + simpl in H. destruct H.
      * inversion H. admit.
      * admit. 
    + admit.
Admitted.


Lemma lemma_9:
  forall left n0 t0 rules,
    ~ In (left, [inl n0; inr t0]) (flat_map normalizeRule rules).
Proof.
  intros left n0 t0 rules contr. induction rules.
  - simpl in contr. assumption.
  - apply IHrules. clear IHrules. destruct a. destruct s.
Admitted.

Lemma lemma_12:
  forall left t0 n0 rules,
    ~ In (left, [inr t0; inl n0]) (flat_map normalizeRule rules).
Proof. Admitted.

Lemma lemma_13:
  forall left t0 t1 rules,
    ~ In (left, [inr t0; inr t1]) (flat_map normalizeRule rules).
Proof. Admitted.

Lemma Alg_prop_7:
forall g left n0 t0,
  ~ In (left, [inl n0; inr t0]) (rules (renameTerms g)).
Proof. intros. apply lemma_9. Qed.

Lemma Alg_prop_8:
forall g left t0 n0,
 ~ In (left, [inr t0; inl n0]) (rules (renameTerms g)).
Proof. intros. apply lemma_12. Qed.

Lemma Alg_prop_9:
forall g left t0 t1,
  ~ In (left, [inr t0; inr t1]) (rules (renameTerms g)).
Proof. intros. apply lemma_13. Qed.



(* TODO:  form. *)
Theorem eq_rename:
  forall g, 
    short_rules g /\ short_rules (renameTerms g) ->
      g_equiv g (renameTerms g).
Proof.
unfold g_equiv. unfold produces. unfold generates. unfold short_rules. simpl. split.
- intros.
  induction H0.
  + apply derives_refl.
  + assert (H' := H1).
    apply H in H1.
    inversion H1.

    destruct right. inversion H3. destruct right. inversion H3. destruct right.
    destruct s0; destruct s4.

    * inversion H3. eapply derives_step. apply IHderives.

    apply -> Alg_prop_3. assumption.

    * destruct t0.
    apply Alg_prop_4 in H'. destruct H'.

    apply derives_trans with (s2 := s2 ++ [inl n; inl (NT ("New_" ++ s0))] ++ s3).
    eapply derives_step. apply IHderives. assumption.

    rewrite <- custom_ass_1 with (s1 := s2) (c1 := inl n) (c2 := inr (T s0)) (s2 := s3).

    apply derives_step with 
    (g := (renameTerms g))
    (s1 := (s2 ++ [inl n; inl (NT ("New_" ++ s0))] ++ s3))
    (s2 := s2 ++ [inl n]) (s3 := s3) (left := (NT ("New_" ++ s0))) (right := [inr (T s0)]).


    rewrite <- custom_ass_1.

    apply derives_refl.
    assumption.

    * destruct t0.
      apply Alg_prop_5 in H'. destruct H'.
      apply derives_trans with (s2 := s2 ++ [inl (NT ("New_" ++ s0)); inl n] ++ s3).
      eapply derives_step. apply IHderives. assumption.


      apply derives_step with 
      (g := (renameTerms g))
      (s1 := (s2 ++ [inl (NT ("New_" ++ s0))] ++ [inl n] ++ s3))
      (s2 := s2) (s3 := [inl n] ++ s3) (left := (NT ("New_" ++ s0))) (right := [inr (T s0)]).


      apply derives_refl.
      assumption.

    * destruct t0. destruct t1.

      apply Alg_prop_6 in H'. destruct H'. destruct H4.

      apply derives_trans with (s2 := s2 ++ [inl (NT ("New_" ++ s0)); inl (NT ("New_" ++ s4))] ++ s3).
      apply derives_step with (left := left). assumption. assumption.

      apply derives_trans with (s2 := s2 ++ [inr (T s0); inl (NT ("New_" ++ s4))] ++ s3).
      apply derives_step with
      (g := (renameTerms g))
      ( s1:= (s2 ++ [inl (NT ("New_" ++ s0)); inl (NT ("New_" ++ s4))] ++ s3))
      (s2:=s2)
      (s3:= [inl (NT ("New_" ++ s4))] ++ s3)
      (left := NT ("New_" ++ s0)) (right := [inr (T s0)]).

      apply derives_refl.
      assumption.

      rewrite <- custom_ass_1 with (s1 := s2) (c1 := inr (T s0)) (c2 := inr (T s4)) (s2 := s3).

      apply derives_step with
      (g := (renameTerms g))
      (s1:= (s2 ++ [inr (T s0); inl (NT ("New_" ++ s4))] ++ s3))
      (s2:= s2 ++ [inr (T s0)])
      (s3:= s3)
      (left := NT ("New_" ++ s4)) (right := [inr (T s4)]).
      rewrite <- custom_ass_3.
      apply derives_refl. assumption.



    * inversion H3.
    * inversion H3. destruct right. inversion H5. destruct right. destruct s0.
      eapply derives_step. apply IHderives. apply -> Alg_prop_2. assumption.

      eapply derives_step. apply IHderives.  apply -> Alg_prop_2. assumption.

      inversion H5.

      inversion H5. destruct right.
      eapply derives_step. apply IHderives. apply -> Alg_prop_1. assumption.
      inversion H7.

- intros. induction H0.
  + apply derives_refl.
  + assert (H' := H1). apply H in H1. inversion H1.

  destruct right. inversion H3. destruct right. inversion H3. destruct right.
  destruct s0; destruct s4.
  * apply derives_step with (left := left). assumption. apply Alg_prop_3. assumption.
  * apply Alg_prop_7 in H'. inversion H'.
  * apply Alg_prop_8 in H'. inversion H'.
  * apply Alg_prop_9 in H'. inversion H'.
  * inversion H3.
  * inversion H3. destruct right. inversion H5.
  destruct right.
  apply derives_step with (left := left). assumption.

  apply <- Alg_prop_2. assumption.

  inversion H5.
  inversion H5. destruct right. apply derives_step with (left := left). assumption.

  apply <- Alg_prop_1. assumption.
  inversion H7. 
Qed.
