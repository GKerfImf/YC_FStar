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

Theorem equivalence:
  forall g,
      g_equiv g (new_s_s g).
Proof.
  unfold g_equiv. unfold produces. unfold generates. simpl. split.
  - admit.
    (* TODO: derives_left *)
    (* TODO: g1 in g2 -> derives g1 a b -> derives g2 a b *) 
  - intros.
    induction H.
    + (* TODO: ??? *) admit.
    + simpl in H0. destruct H0. inversion H0. subst.
      (* H : derives (new_s_s g) s1 (s2 ++ inl (new_name (start_symbol g)) :: s3) ~ False *) admit.
      apply derives_step with (left := left). assumption. assumption.
Admitted.

