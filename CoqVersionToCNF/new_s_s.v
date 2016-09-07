Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Core.


Definition g1 := {|
  start_symbol := NT "S";
  rules := [
    (NT "S", [inr (T "("); inl (NT "S"); inr (T ")")]); 
    (NT "S", [inl (NT "S"); inl (NT "S")]); 
    (NT "S", [inr (T "O")])
  ];
|}.
Definition new_name (ss: nt) :=
  match ss with
  | NT s => NT (s ++ "'")
  end.

Definition new_s_s (g: cfg) := {|
  start_symbol := new_name (start_symbol g);
  rules := (new_name (start_symbol g), [inl (start_symbol g)])::(rules g)
|}.

Compute (new_s_s g1).

Definition well_named_left_local (g: cfg) :=
  forall (left: nt) (right: sf),
    In (left,right) (rules g) ->
    left <> new_name (start_symbol g).

Definition well_named_right_local (g: cfg) :=
  forall (left: nt) (right: sf),
    In (left,right) (rules g) ->
    (forall nt, In nt right -> nt <> inl (new_name (start_symbol g))).

(* Definition well_named_local (g: cfg) :=
  well_named_left_local g /\ well_named_right_local g. *)

Theorem progress:
  forall (g:cfg) (left: nt) (right: sf),
    well_named_left_local g ->
    In (left,right) (rules (new_s_s g)) ->
    left = (start_symbol (new_s_s g)) ->
    right = [inl (start_symbol g)].
Proof.
  intros g l r WN H0 H1.
  unfold well_named_left_local in WN.
  simpl in H0.
  destruct H0.
  - inversion_clear H. reflexivity.
  - apply WN in H. subst. destruct H. simpl. reflexivity.
Qed.

Lemma lemma_5:
  forall nt,
    nt <> new_name nt.
Proof.
  intros nt contra.
  destruct nt. unfold new_name in contra.
  inversion contra.
  clear contra. induction s.
  - inversion H0.
  - inversion H0. auto.
Qed.

Theorem progress':
  forall (g:cfg) (rule: nt * sf),
    well_named_right_local g ->
    In rule (rules (new_s_s g)) ->
    ~ (In (inl (start_symbol (new_s_s g))) (snd rule)).
Proof.
  intros g rule WN2 H contra.
  unfold well_named_right_local in WN2.
  destruct rule.
  simpl in *.
  destruct H.
  - inversion H. subst. destruct contra.
    + inversion H0. apply lemma_5 in H2. assumption.
    + inversion H0.
  - apply WN2 with (nt0 := inl (new_name (start_symbol g)))in H.
    + unfold not in H. apply H. reflexivity.
    + assumption.
Qed.

Lemma lemma_1:
  forall g left right, In (left, right) (rules g) -> In (left, right) (rules (new_s_s g)).
Proof.
  Admitted.

Lemma lemma_2:
  forall g g' s,
    derives g [inl (start_symbol g)] (map terminal_lift s) ->
    (forall rule, In rule (rules g) -> In rule (rules g')) ->
    derives g' [inl (start_symbol g)] (map terminal_lift s).
Proof. Admitted.

Lemma lemma_3:
  forall g s,
    derives g [inl (start_symbol g)] (map terminal_lift s) ->
    derives (new_s_s g) [inl (start_symbol g)] (map terminal_lift s).
Proof.
  intros.
  apply lemma_2.
  - assumption.
  - intros.
    simpl. right. assumption. Qed.

(* Lemma lemma_4:
g : cfg
s : list t
H : derives (new_s_s g)
      [inl (new_name (start_symbol g))]
      (map terminal_lift s)
______________________________________(1/1)
derives g [inl (start_symbol g)]
  (map terminal_lift s)
 *)
Theorem equivalence:
  forall g,
      g_equiv g (new_s_s g).
Proof.
  unfold g_equiv. unfold produces. unfold generates. simpl. split.
  - intros.
    apply derives_left with (g := new_s_s g) (s1 := []) (right := [inl (start_symbol g)]).
    + simpl. apply lemma_3. assumption.
    + simpl. left. reflexivity.
  - intros.
(*     simpl in H.
    apply derives_left with (g := new_s_s g) (s1 := []) (right := [inl (start_symbol g)]) in H. with
      (g := new_s_s g)
      (s1 := [inl (new_name (start_symbol g))])
      (s2 := []) 
      (s3 := [])
      (left := (new_name (start_symbol g)))
      (right := [inl (start_symbol g)])  in H. *)
    destruct H.
    + (* TODO: ??? *) admit.
    + simpl in H0. destruct H0. inversion H0. subst.
      (* H : derives (new_s_s g) s1 (s2 ++ inl (new_name (start_symbol g)) :: s3) ~ False *) admit.
      apply derives_step with (left := left). assumption. assumption.
Admitted.

