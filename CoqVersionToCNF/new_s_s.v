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
  | NT s => NT (s ++ "0")
  end.

Definition new_s_s (g: cfg) := {|
  start_symbol := new_name (start_symbol g);
  rules := (new_name (start_symbol g), [inl (start_symbol g)])::(rules g)
|}.

Compute (new_s_s g1).

Theorem progress:
  forall (g:cfg) (rule: nt * sf),
  (* TODO: some name-restr. *)
  In rule (rules (new_s_s g)) -> ~ (In (inl (start_symbol (new_s_s g))) (snd rule)).
Proof.
  intros g rule H contra.
  simpl in *.
  destruct H.
  - subst. simpl in *. destruct contra.
    + destruct g. simpl in H. inversion H. admit.
    + inversion H.
  - admit.
Admitted.



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
    induction H.
    + (* TODO: ??? *) admit.
    + simpl in H0. destruct H0. inversion H0. subst.
      (* H : derives (new_s_s g) s1 (s2 ++ inl (new_name (start_symbol g)) :: s3) ~ False *) admit.
      apply derives_step with (left := left). assumption. assumption.
Admitted.

