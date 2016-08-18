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
  (* rules_short := short_r1 *)
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

Definition isSingle (rule: (nt * (list (nt + t)))) :=
    match rule with
    | (_,[inr _]) => true
    | _ => false
    end.

Definition isToken (elem: (nt + t)) :=
    match elem with
    | inl _ => false
    | inr _ => true
    end.

Definition getNewText (elem: (nt + t)): string :=
    match elem with
    | inr (T s) => "New_" ++ s
    | _ => ""
    end.

Definition renameElem (rule: (nt * (list (nt + t)))) (elem: (nt + t)) : ((nt + t) * (list (nt *(list (nt + t))))) :=
    if isToken elem then
      ( inl (NT ( getNewText elem ) ) , [ ( NT ( getNewText elem ), [ elem ] ) ] )
    else ( elem, [] ).


Definition renameRule (rule: (nt * (list (nt + t)))) : ( list ((nt * (list (nt + t)))) ) :=
  let res := map (renameElem rule) (snd rule) in
	match rule with
	| (l,r) => (l, map fst res):: flat_map snd res
  end.

Definition normalizeRule (rule: (nt * (list (nt + t)))) : ( list ((nt * (list (nt + t)))) ) :=
  if isSingle rule then [rule] else renameRule rule.



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

Lemma test_40:
  forall (g: cfg) (r: rule) (left: nt) (right: sf),
    In r (rules g) ->
    forall rn, In rn (normalizeRule r) -> In rn (rules (renameTerms g)).
Proof.
  intros. destruct r. destruct rn. unfold normalizeRule in H0. destruct isSingle.
  + inversion_clear H0. admit. inversion H1.
  + Admitted.

(* Theorem derives_rule:
forall g: cfg,
forall left: nt,
forall right s1 s2: sf,
In (left,right) (rules g) ->
derives g (s1 ++ [inl left] ++ s2) (s1 ++ right ++ s2).
Proof. Admitted. *)


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
  forall g left r_single,
  In (left, [r_single]) (rules g) <->
  In (left, [r_single]) (rules (renameTerms g)).
Proof.
  split.
  - intros. apply test_40 with (rn:= (left,[r_single])) (r := (left,[r_single])) in H. assumption. assumption. admit.
    destruct r_single. simpl. left. reflexivity.
    simpl. left. reflexivity.
  - intros.
     Admitted.

Lemma Alg_prop_2:
  forall g left,
  In (left, []) (rules g) <->
  In (left, []) (rules (renameTerms g)).
Proof.
  split.
  - intros.
    apply test_40 with (rn:= (left,[])) (r := (left,[]) ) in H. assumption. auto. admit.
    simpl. left. reflexivity.
  - intros.
       Admitted.

Lemma Alg_prop_3:
  forall g left n0 n1,
  In (left, [inl n0; inl n1]) (rules g) <->
  In (left, [inl n0; inl n1]) (rules (renameTerms g)).
Proof. Admitted.

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
  intros g left n0 t0 contr.

  induction (rules (renameTerms g)). inversion contr. apply IHl.
  destruct contr.
  unfold renameTerms in contr.
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
      eapply derives_step. apply IHderives. apply -> Alg_prop_1. assumption.

      eapply derives_step. apply IHderives.  apply -> Alg_prop_1. assumption.

      inversion H5.

      inversion H5. destruct right.
      eapply derives_step. apply IHderives. apply -> Alg_prop_2. assumption.
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

  apply <- Alg_prop_1. assumption.

  inversion H5.
  inversion H5. destruct right. apply derives_step with (left := left). assumption.

  apply <- Alg_prop_2. assumption.
  inversion H7. 
Qed.

