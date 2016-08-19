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

Definition short_rules_def (rules: list rule) :=
  forall left (right: sf), In (left,right) rules -> length right <= 2.

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

Definition r1 := [
  (NT "A", [inr (T "a"); inl (NT "B")]); 
  (NT "B", [inl (NT "C")]);
  (NT "C", [inr (T "c")])
].

Lemma short_r1 :
  short_rules_def r1.
Proof.
  unfold short_rules_def.
  intros. unfold r1 in H.
  inversion_clear H. inversion H0. auto.
  inversion_clear H0. inversion H. auto.
  inversion_clear H. inversion H0. auto.
  inversion H0. Qed.

Definition g1 := {|
  start_symbol := NT "A";
  rules := r1
|}.

Lemma test_0:
  derives g1 [inl (NT "S")] [inl (NT "S")].
Proof. apply derives_refl. Qed.


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

Definition renameElem (rule: nt * sf) (elem: nt + t) : ((nt + t) * (list (nt *sf))) :=
  match elem with
  | inr t => ( inl (NT ( getNewText t ) ) , [ ( NT ( getNewText t ), [ elem ] ) ] )
  | inl _ => ( elem, [] )
  end.


Definition renameRule (rule: nt * sf) : ( list (nt * sf) ) :=
  let res := map (renameElem rule) (snd rule) in
	match rule with
	| (l,r) => (l, map fst res):: flat_map snd res
  end.
  
Lemma test_41:
  forall left nt0,
  renameRule (left,[inl nt0]) = [(left,[inl nt0])].
Proof.
  intros. unfold renameRule. simpl. reflexivity. Qed.

Lemma test_42:
  forall left,
  renameRule (left,[]) = [(left,[])].
Proof.
  intros. unfold renameRule. simpl. reflexivity. Qed.


Definition normalizeRule (rule: nt * sf) : ( list (nt * sf) ) :=
  if isSingle rule then [rule] else renameRule rule.

Lemma test_40:
  forall rule,
  isSingle rule = true ->
  normalizeRule rule = [rule].
Proof.
  intros. unfold normalizeRule. destruct isSingle. reflexivity. inversion H. Qed.


Lemma test_43:
  forall left t0,
  normalizeRule (left,[inr t0]) = [(left,[inr t0])].
Proof.  intros. reflexivity. Qed.

Lemma test_44:
  forall left nt0,
  normalizeRule (left,[inl nt0]) = [(left,[inl nt0])].
Proof.
  intros. reflexivity. Qed.


Lemma test_45:
  forall left,
  normalizeRule (left,[]) = [(left,[])].
Proof.
  intros. reflexivity. Qed.
  
Lemma test_46:
  forall left single,
  normalizeRule (left,[single]) = [(left,[single])].
Proof.
  intros. destruct single. reflexivity. reflexivity. Qed.

Lemma lemma_1:
  forall (A: Type) (x: A) (l1: list A) (l2: list A),
  In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros. generalize dependent l2.
  induction l1.
  - simpl.
    split.
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

Lemma test_49:
  forall (A:Type) (f: A -> list A) (x:A) (xs: list A),
    f x = [x] ->
    In x xs ->
    In x (flat_map f xs).
Proof.
  intros. induction xs.
    + inversion H0.
    + simpl. apply lemma_1. assert (a :: xs = [a] ++ xs). simpl. reflexivity. rewrite H1 in H0.
      apply lemma_1 in H0.
      destruct H0.
      * inversion H0. subst. left. rewrite H. assumption. simpl. inversion H2.
      * right. apply IHxs. assumption.
Qed.

Lemma test_50:
  forall (A:Type) (f: A -> list A) (x:A) (xs: list A),
    f x = [x] ->
    (forall x', In x (f x') -> x = x') ->
    In x (flat_map f xs) ->
    In x xs.
Proof.
  intros. induction xs.
  - inversion H1.
  - simpl in H1. apply lemma_1 in H1. destruct H1.
    + apply H0 in H1. subst. simpl. left. reflexivity.
    + simpl. right. apply IHxs. assumption.
Qed.


Lemma lemma_3 :
  forall left x,
    In (left, []) (normalizeRule x) -> (left, []) = x.
Proof. Admitted.

Lemma test_47:
  forall left rules,
  In (left,[]) rules <-> In (left,[]) (flat_map normalizeRule rules).
Proof.
  intros. split.
  - apply test_49. reflexivity.
  - apply test_50. reflexivity. apply lemma_3. Qed.

Lemma test_51:
  forall left single rules,
  In (left, [single]) (flat_map normalizeRule rules) <-> In (left,[single]) rules.
Proof.
  intros. split.
  - apply test_50.
    + apply test_46.
    + admit.
  - apply test_49. apply test_46. Admitted.


Definition renameTerms (g: cfg) := {|
  start_symbol := start_symbol g;
  rules := flat_map normalizeRule (rules g)
|}.

(* Lemma test_38:
  forall g left right, 
    In (left,right) (rules g) ->
    isSingle (left, right) = true ->
    forall leftR rightR, In (leftR,rightR) (normalizeRule (left,right)) ->
    left = leftR /\ right = rightR.
Proof.
  intros.
  unfold normalizeRule in H1. destruct isSingle.
  + inversion H1. inversion H2. auto. inversion H2.
  + inversion H0.
Qed.
Lemma test_39:
  forall g left right, 
    In (left,right) (rules g) ->
    isSingle (left, right) = false ->
    forall leftR rightR, In (leftR,rightR) (normalizeRule (left,right)) ->
    In (leftR,rightR) (renameRule (left,right)).
Proof.
  intros.
  unfold normalizeRule in H1. destruct isSingle.
  + inversion H0.
  + assumption.
Qed. *)

(* forall g: cfg _ _,
forall left: non_terminal,
forall right s1 s2: sf,
rules g left right ->
derives g (s1 ++ [inl left] ++ s2) (s1 ++ right ++ s2). *)

Definition short_rules (g: cfg) :=
  forall left right, 
    In (left, right) (rules g) -> length right <= 2.

(* Lemma test_52:
  forall (g: cfg) (r: rule) (left: nt) (right: sf),
    In r (rules g) ->
    forall rn, In rn (normalizeRule r) -> In rn (rules (renameTerms g)).
Proof.
  intros. destruct r. destruct rn. unfold normalizeRule in H0. destruct isSingle.
  + inversion_clear H0. admit. inversion H1.
  + Admitted. *)


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
  - apply test_49. apply test_45.
  - apply test_47. Qed.

Lemma Alg_prop_2:
  forall g left r_single,
  In (left, [r_single]) (rules g) <->
  In (left, [r_single]) (rules (renameTerms g)).
Proof.
  split.
  - apply test_49. apply test_46.
  - apply test_51. Qed.

Lemma Alg_prop_3:
  forall g left n0 n1,
  In (left, [inl n0; inl n1]) (rules g) <->
  In (left, [inl n0; inl n1]) (rules (renameTerms g)).
Proof.
  split.
  - apply test_49.
    unfold normalizeRule. simpl. reflexivity.
  - apply test_50. unfold normalizeRule. simpl. reflexivity.
    admit. Admitted.

Lemma Alg_prop_4:
  forall g left n s0,
    In (left, [inl n; inr (T s0)]) (rules g) ->
    In (left, [inl n; inl (NT ("New_" ++ s0))]) (rules (renameTerms g)) /\ In (NT ("New_" ++ s0), [inr (T s0)]) (rules (renameTerms g)).
Proof. Admitted.

Lemma Alg_prop_5:
forall g left n s0,
In (left, [inr (T s0); inl n]) (rules g) ->
In (left, [inl (NT ("New_" ++ s0)); inl n]) (rules (renameTerms g)) /\ In (NT ("New_" ++ s0), [inr (T s0)]) (rules (renameTerms g)).
Proof. Admitted.

Lemma Alg_prop_6:
forall g left s0 s1,
In (left, [inr (T s0); inr (T s1)]) (rules g) ->
In (left, [inl (NT ("New_" ++ s0)); inl (NT ("New_" ++ s1))]) (rules (renameTerms g)) 
/\ In (NT ("New_" ++ s0), [inr (T s0)]) (rules (renameTerms g))
/\ In (NT ("New_" ++ s1), [inr (T s1)]) (rules (renameTerms g)).
Proof. Admitted.

Lemma Alg_prop_7:
forall g left n0 t0,
  ~ In (left, [inl n0; inr t0]) (rules (renameTerms g)).
Proof.
  intros g left n0 t
 Admitted.

Lemma Alg_prop_8:
forall g left t0 n0,
 ~ In (left, [inr t0; inl n0]) (rules (renameTerms g)).
Proof. Admitted.

Lemma Alg_prop_9:
forall g left t0 t1,
  ~ In (left, [inr t0; inr t1]) (rules (renameTerms g)).
Proof. Admitted.



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


(* 
Theorem eq_rename:
  forall g,
      g_equiv g (renameTerms g).
Proof.
  unfold g_equiv. unfold produces. unfold generates. unfold short_rules. simpl. split.
  - intros. induction H.
    + apply derives_refl.
    + generalize dependent s1. generalize dependent s2. generalize dependent s3. induction right. intros.
      * apply derives_step with (left := left). assumption. apply test_49. reflexivity. assumption.
      * intros.
        apply derives_step with (right := a :: right) in H.
        replace (s2 ++ (a :: right) ++ s3) with ((s2 ++ [a]) ++ right ++ s3).
        apply IHright with (s1 := s1) (s2 := s2 ++ [a]) (s3 := s3).
         admit.
        assumption.
Admitted. *)