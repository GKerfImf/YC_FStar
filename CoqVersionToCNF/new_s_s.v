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

(* Lemma lemma_1:
  forall g left right, In (left, right) (rules g) -> In (left, right) (rules (new_s_s g)).
Proof.
  Admitted.
 *)
Lemma lemma_2:
  forall g g' s,
    derives g [inl (start_symbol g)] (map terminal_lift s) ->
    (forall rule, In rule (rules g) -> In rule (rules g')) ->
    derives g' [inl (start_symbol g)] (map terminal_lift s).
Proof.
  intros.
  induction H.
  - apply derives_refl.
  - apply derives_trans with (s2 := s2 ++ inl left :: s3).
    + apply IHderives.
    + apply derives_step with (left := left).
      * apply derives_refl.
      * apply H0. apply H1.
Qed.

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

Theorem derives_rule:
  forall g left right s1 s2,
    In (left,right) (rules g) ->
    derives g (s1 ++ [inl left] ++ s2) (s1 ++ right ++ s2).
Proof.
  intros g left right s1 s2 H.
  apply derives_step with (left:=left).
  - apply derives_refl.
  - exact H.
Qed.

Theorem derives_start:
  forall g left right,
    In (left,right) (rules g) -> derives g [inl left] right.
Proof.
  intros g left right H.
  apply derives_rule with (s1:=[]) (s2:=[]) in H.
  simpl in H.
  rewrite app_nil_r in H.
  exact H.
Qed.
    
Lemma lemma_8:
  forall g s (l:nt) r,
    derives g [inl l] s ->
    In (l,r) (rules g) ->
    (forall l' r', In (l',r') (rules g) -> l = l' -> r = r') ->
    s = r.
Proof.
  intros. apply derives_start in H0.
  destruct s. admit. inversion H.
  apply H1 in H0.
  apply derives_step with (s2 := []) (right := []) (s3 := []) in H.
Admitted.

Lemma lemma_7:
  forall g s (l:nt) r,
    derives g [inl l] s ->
    In (l,r) (rules g) ->
    (forall l' r', In (l',r') (rules g) -> l = l' -> r = r') ->
    derives g r s.
Proof.
  intros.
  apply lemma_8 with (r := r) in H. 
  - subst. apply derives_refl.
  - assumption.
  - assumption.
Qed.

Lemma lemma_4:
  forall (g: cfg) s,
    well_named_left_local g ->
    derives (new_s_s g) [inl (new_name (start_symbol g))] s ->
    derives (new_s_s g) [inl (start_symbol g)] s.
Proof.
  intros.
  apply lemma_7 with (r := [inl (start_symbol g)]) in H0.
  + simpl. assumption.
  + simpl. left. reflexivity.
  + intros. subst. destruct H1. inversion H1. subst. reflexivity.
    unfold well_named_left_local in H. apply H in H1. unfold not in H1. exfalso. apply H1. reflexivity.
Qed.

Lemma lemma_6:
  forall g s1 s2 s3,
  ~ (derives (new_s_s g) s1
      (s2 ++ inl (new_name (start_symbol g)) :: s3)).
Proof.
  intros g s1 s2 s3 c.
Admitted.

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
    apply lemma_4 in H.
    induction H.
    apply derives_refl.
    apply derives_trans with (s2 := (s2 ++ inl left :: s3)).
    + assumption.
    + clear IHderives. simpl in H0. destruct H0.
      * inversion H0. subst. clear H0. apply lemma_6 in H. inversion H.
      * apply derives_step with (left := left). apply derives_refl. assumption.
Qed.

