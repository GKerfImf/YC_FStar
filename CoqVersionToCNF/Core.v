Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.


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

Theorem derives_left (g: cfg) (left: nt) (right: sf) (s1 s2 s3: sf):
  derives g (s1 ++ right ++ s2) s3 ->
  In (left,right) (rules g) ->
  derives g (s1 ++ inl left :: s2) s3.
Proof.
  intros.
  apply derives_trans with (s2 := s1 ++ right ++ s2).
  - apply derives_step with (left := left).
    + apply derives_refl.
    + assumption.
  - assumption.
Qed.

(* Theorem derives_left2 (g: cfg) (left: nt) (right: sf) (s1 s2 s3: sf):
  derives g (s1 ++ inl left :: s2) s3 ->
  In (left,right) (rules g) ->
  (forall l' r', In (l',r') (rules g) -> left = l' -> r' = right) -> (* exists! *)
  derives g (s1 ++ right ++ s2) s3.
Proof.
  intros.
  apply derives_trans with (s1 := s1 ++ inl left :: s2) in H.
  apply derives_left with (s1 := s1) (right := inl left) in H.
Admitted. *)

Definition generates (g: cfg) (s: list (nt + t)): Prop:=
  derives g [inl (start_symbol g)] s.

Definition produces (g: cfg) (s: list t): Prop:=
  generates g (map terminal_lift s).

Definition g_equiv (g1: cfg) (g2: cfg): Prop:=
  forall s: list t, produces g1 s <-> produces g2 s.