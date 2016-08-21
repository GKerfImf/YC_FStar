Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.EqNat.
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


Definition renameElem1 (elem: nt + t) : ((nt + t)) :=
  match elem with
  | inr t => inl (NT ( getNewText t ) ) 
  | inl _ => elem
  end.
Definition renameElem2 (elem: nt + t) : ((list (nt *sf))) :=
  match elem with
  | inr t => (  [ ( NT ( getNewText t ), [ elem ] ) ] )
  | inl _ => ( [] )
  end.


Definition renameRule (rule: nt * sf) : ( list (nt * sf) ) :=
	match rule with
	| (l,r) => (l, map renameElem1 (snd rule)) :: flat_map renameElem2 (snd rule)
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

Lemma destr_isSingle_lemma:
  forall x, { isSingle x = true } + { isSingle x = false}.
Proof.
  intros. destruct x. destruct s; auto. destruct s; auto. destruct s0; auto. Qed.

Lemma custom_ass_1: forall (A:Type) (c1 c2: A) (s1 s2: list A), 
(s1 ++ [c1]) ++ [c2] ++ s2 = s1 ++ [c1; c2] ++ s2 .
Proof. intros. simpl. rewrite <- app_assoc with (l := s1) (m := [c1]) (n := c2 :: s2). reflexivity. Qed.

Lemma custom_ass_2: forall (A:Type) (c1 c2: A) (s1 s2: list A), 
s1 ++ [c1] ++ [c2] ++ s2 = (s1 ++ [c1; c2] ++ s2) .
Proof. intros. simpl. reflexivity. Qed.

Lemma custom_ass_3: forall (A:Type) (c1 c2: A) (s1 s2: list A),
(s1 ++ [c1]) ++ c2 :: s2 = s1 ++ [c1; c2] ++ s2.
Proof. intros. simpl. apply custom_ass_1. Qed.

Lemma map_length:
  forall (A B:Type) (f: A -> B) (xs: list A) (ys: list B),
  map f xs = ys -> length xs = length ys.
Proof.
  debug auto.
  intros. generalize dependent ys. 
  induction xs; intros; inversion H; simpl in *; auto. Qed.

(* ---------------------------------------------------------------------------------- *)

Lemma invar_eps_lemma:
  forall left,
  normalizeRule (left,[]) = [(left,[])].
Proof. intros. reflexivity. Qed.


Lemma invar_single_lemma:
  forall left single,
  normalizeRule (left,[single]) = [(left,[single])].
Proof.
  intros. destruct single. reflexivity. reflexivity. Qed.


Lemma invar_2nonterm_lemma:
  forall left n0 n1,
  normalizeRule (left, [inl n0; inl n1]) = [(left, [inl n0; inl n1])].
Proof. intros. reflexivity. Qed.


Lemma h_integr_eps:
  forall left rule,
    In (left, []) (renameRule rule) -> rule = (left,[]).
Proof.
  intros. destruct rule0. destruct s.
  - simpl in H. destruct H. assumption. inversion H.
  - simpl in H. destruct H.
    + inversion H.
    + apply concat_in_lemma in H. destruct H.
      * destruct s.
        -- simpl in H. inversion H. 
        -- simpl in H. destruct H. inversion H. inversion H.
      * induction s0. simpl in H. inversion H. destruct a.
        -- simpl in H. apply IHs0 in H. inversion H.
        -- simpl in H. destruct H. inversion H. apply IHs0 in H. inversion H.
Qed.

Lemma integr_eps_lemma:
  forall left rule,
    In (left, []) (normalizeRule rule) -> (left, []) = rule.
Proof.
  intros.
  unfold normalizeRule in H. destruct isSingle in H.
  - inversion H. auto. inversion H0.
  - destruct rule0. apply h_integr_eps in H. inversion H. reflexivity. 
Qed.


Lemma hh_integr_nt_sinle:
  forall left nt0 elems,
  ~ In (left, [inl nt0]) (flat_map renameElem2 elems).
Proof. 
  intros left nt0 elems contra. induction elems.
  - inversion contra.
  - simpl in contra. apply concat_in_lemma in contra. destruct contra.
    + destruct a.  inversion H. inversion H. inversion H0. inversion H0.
    + apply IHelems in H. inversion H.
Qed.

Lemma h_integr_nt_sinle:
  forall left nt0 rule,
    In (left,[inl nt0]) (renameRule rule) -> isSingle rule = false -> (left,[inl nt0]) = rule.
Proof.
  intros. destruct rule0. destruct H.
  - inversion H. subst.
      destruct s. inversion H3.
      destruct s0. destruct s. simpl. reflexivity. inversion H3. inversion H0. inversion H3. 
  - apply hh_integr_nt_sinle in H. inversion H.
Qed.

Lemma integr_nt_sinle_lemma :
  forall left nt0 x,
    In (left,[inl nt0]) (normalizeRule x) -> (left,[inl nt0]) = x.
Proof.
  intros. unfold normalizeRule in H. edestruct destr_isSingle_lemma; rewrite e in H.
  - inversion H. auto. inversion H0.
  - apply h_integr_nt_sinle. assumption. assumption. Qed.


Lemma hh_integr_t_sinle:
  forall name t0 elems,
  (forall s, name <> append "New_" s) ->
  ~ In (NT name, [inr t0]) (flat_map renameElem2 elems).
Proof.
  intros t0 s0 elems KN contra.
  induction elems.
  - inversion contra.
  - simpl in contra. apply concat_in_lemma in contra. destruct contra.
    + destruct a.
      * inversion H.
      * inversion H. inversion H0. destruct t1. simpl in H2. unfold not in KN. symmetry in H2.
        apply KN in H2. inversion H2. simpl in KN. inversion H0.
    + apply IHelems in H. inversion H.
Qed.

Lemma h_integr_t_sinle:
  forall (left:nt) (t0:t) (elems: list (nt + t)),
  (forall s, left <> NT ("New_" ++ s)) ->
  ~ In (left, [inr t0]) (flat_map renameElem2 elems).
Proof.
  intros.
  destruct left. apply hh_integr_t_sinle. unfold not in *. intros. 
  assert (H' := H). apply H with (s0 := s0). subst. reflexivity.
Qed.

Lemma integr_t_sinle_lemma :
  forall left t0 x,
    (forall s, left <> NT ("New_" ++ s)) ->
    In (left,[inr t0]) (normalizeRule x) -> (left,[inr t0]) = x.
Proof.
  intros. unfold normalizeRule in H0. destruct isSingle.
  - inversion H0. auto. inversion H1.
  - intros. destruct x. destruct H0.
    + inversion H0. subst.
        destruct s. inversion H3.
        destruct s0. destruct s. simpl. reflexivity. inversion H3. inversion H0.
    + simpl in H0. apply h_integr_t_sinle in H0. inversion H0. assumption. Qed.


Lemma integr_sinlge_lemma :
  forall left single rule,
    (forall s, left <> NT ("New_" ++ s)) ->
    In (left, [single]) (normalizeRule rule) ->
    (left, [single]) = rule.
Proof.
  intros.
  destruct single.
    apply integr_nt_sinle_lemma. assumption.
    apply integr_t_sinle_lemma. assumption. assumption.
Qed.


Lemma h_integr_nt_nt:
  forall rule elems,
    length (snd rule) >= 2 -> ~ In rule (flat_map renameElem2 elems).
Proof.
  unfold not. intros.
  destruct rule0. simpl in H.
  induction elems.
  - inversion H0.
  - simpl in H0. apply concat_in_lemma in H0. destruct H0.
    + destruct a.
      * inversion H0.
      * simpl in H0. destruct H0.
        -- inversion H0. subst. inversion H. inversion H2.
        -- inversion H0.
    + apply IHelems in H0. inversion H0. Qed.

Lemma integr_nt_nt_lemma:
  forall left n0 n1 rule,
    (forall s, left <> NT ("New_" ++ s)) ->
    (forall s, n0 <> NT ("New_" ++ s)) ->
    (forall s, n1 <> NT ("New_" ++ s)) ->
    In (left, [inl n0; inl n1]) (normalizeRule rule) ->
    (left, [inl n0; inl n1]) = rule.
Proof.
  intros left n0 n1 rule NL N0 N1 H.
  unfold normalizeRule in H. destruct isSingle.
  - destruct H. auto. inversion H.
  - destruct rule. simpl in H. destruct H.
    + inversion H.
      destruct s. inversion_clear H.
      destruct s0. inversion_clear H.
      destruct s1. inversion H2.
        destruct s; destruct s0.
        * simpl. reflexivity.
        * simpl in H4. inversion H4. symmetry in H5. destruct t0. simpl in H5. apply N1 in H5. inversion H5.
        * simpl in H3. inversion H3. symmetry in H5. destruct t0. simpl in H5. apply N0 in H5. inversion H5.
        * simpl in H3. inversion H3. symmetry in H5. destruct t0. simpl in H5. apply N0 in H5. inversion H5.
        * inversion H2.
    + apply h_integr_nt_nt in H. inversion H. simpl. auto. Qed.


Definition renameTerms (g: cfg) := {|
  start_symbol := start_symbol g;
  rules := flat_map normalizeRule (rules g)
|}.

Definition short_rules (g: cfg) :=
  forall left right, 
    In (left, right) (rules g) -> length right <= 2.


Lemma Alg_prop_1:
  forall g left,
  In (left, []) (rules g) <->
  In (left, []) (rules (renameTerms g)).
Proof.
  intros. split.
  - apply flat_map_lemma_1. reflexivity.
  - apply flat_map_lemma_2. reflexivity. apply integr_eps_lemma. Qed.

Lemma Alg_prop_2:
  forall g left r_single,
  (forall s, left <> NT ("New_" ++ s)) ->
  In (left, [r_single]) (rules g) <->
  In (left, [r_single]) (rules (renameTerms g)).
Proof.
  intros. split.
  - apply flat_map_lemma_1. apply invar_single_lemma.
  - apply flat_map_lemma_2.
    + apply invar_single_lemma.
    + intros. apply integr_sinlge_lemma. assumption. assumption. Qed.

Lemma Alg_prop_3:
  forall g left n0 n1,
    (forall s, left <> NT ("New_" ++ s)) ->
    (forall s, n0 <> NT ("New_" ++ s)) ->
    (forall s, n1 <> NT ("New_" ++ s)) ->
    In (left, [inl n0; inl n1]) (rules g) <->
    In (left, [inl n0; inl n1]) (rules (renameTerms g)).
Proof.
  intros. split.
  - apply flat_map_lemma_1. apply invar_2nonterm_lemma.
  - apply flat_map_lemma_2.
    + apply invar_2nonterm_lemma.
    + intros. apply integr_nt_nt_lemma; assumption.
  Qed.

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




(* -------------------------------------------------------------------------------- *)  
(* -------------------- Ctrl+C Ctrl+V lemma --------------------------------------- *)
(* -------------------------------------------------------------------------------- *)

Lemma renameRule_progress_1_lemma:
  forall left n0 t0 rule,
    ~(In (left, [inl n0; inr t0]) (normalizeRule rule)).
Proof.
  intros left n0 t0 rule contr. destruct rule.
  unfold normalizeRule in contr.
  destruct destr_isSingle_lemma with (x := (n,s)); rewrite e in contr.
  + inversion contr. inversion H. subst. simpl in e. congruence. inversion H.
  + clear e. unfold renameRule in contr. destruct contr; simpl in H.
    - inversion H. clear H H1. assert (H' := H2). apply map_length in H2.
      destruct s. inversion H2. destruct s0. inversion H2. destruct s1.
      * destruct s; destruct s0; simpl in H'; inversion H'. 
      * inversion H2.
    - induction s.
      * inversion H.
      * simpl in H. apply concat_in_lemma in H. destruct H.
        ++ destruct a. simpl in H. inversion H. simpl in H. destruct H. inversion H. inversion H.  
        ++ auto.
Qed.

Lemma renameRule_progress_2_lemma:
  forall left t0 n0  rule,
    ~(In (left, [inr t0; inl n0]) (normalizeRule rule)).
Proof.
  intros left n0 t0 rule contr. destruct rule.
  unfold normalizeRule in contr.
  destruct destr_isSingle_lemma with (x := (n,s)); rewrite e in contr.
  + inversion contr. inversion H. subst. simpl in e. congruence. inversion H.
  + clear e. unfold renameRule in contr. destruct contr; simpl in H.
    - inversion H. clear H H1. assert (H' := H2). apply map_length in H2.
      destruct s. inversion H2. destruct s0. inversion H2. destruct s1.
      * destruct s; destruct s0; simpl in H'; inversion H'. 
      * inversion H2.
    - induction s.
      * inversion H.
      * simpl in H. apply concat_in_lemma in H. destruct H.
        ++ destruct a. simpl in H. inversion H. simpl in H. destruct H. inversion H. inversion H.  
        ++ auto.
Qed.

Lemma renameRule_progress_3_lemma:
  forall left t0 t1  rule,
    ~(In (left, [inr t0; inr t1]) (normalizeRule rule)).
Proof.
  intros left n0 t0 rule contr. destruct rule.
  unfold normalizeRule in contr.
  destruct destr_isSingle_lemma with (x := (n,s)); rewrite e in contr.
  + inversion contr. inversion H. subst. simpl in e. congruence. inversion H.
  + clear e. unfold renameRule in contr. destruct contr; simpl in H.
    - inversion H. clear H H1. assert (H' := H2). apply map_length in H2.
      destruct s. inversion H2. destruct s0. inversion H2. destruct s1.
      * destruct s; destruct s0; simpl in H'; inversion H'. 
      * inversion H2.
    - induction s.
      * inversion H.
      * simpl in H. apply concat_in_lemma in H. destruct H.
        ++ destruct a. simpl in H. inversion H. simpl in H. destruct H. inversion H. inversion H.  
        ++ auto.
Qed.

(* minimized? *)
Lemma renameRule_progress_lemma:
  forall left n0 t0 t1 right rule,
    right = [inr t0; inr t1] \/ right = [inr t0; inl n0] \/ right = [inl n0; inr t0] -> 
    ~(In (left, right) (normalizeRule rule)).
Proof.
  intros left n0 t0 t1 right rule R contr. destruct rule.
  unfold normalizeRule in contr.
  destruct destr_isSingle_lemma with (x := (n,s)); rewrite e in contr.
  + inversion contr. inversion H. subst.
    destruct R; [| destruct H0]; subst; simpl in *; congruence.
    inversion H.
  + clear e. unfold renameRule in contr. destruct contr; simpl in H.
    - inversion H. clear H H1. assert (H' := H2). apply map_length in H2.
      destruct s; [|destruct s0; [|destruct s1]];
      try (destruct R as [L|R]; [|destruct R as [L|R]]; subst; destruct s; destruct s0; simpl in H'; inversion H');
      try (destruct R as [L|R]; [|destruct R as [L|R]]; subst; inversion H2).
    - induction s.
      * inversion H.
      * simpl in H. apply concat_in_lemma in H. destruct H.
        ++ destruct R as [L|R]; [|destruct R as [L|R]]; subst; 
            destruct a; simpl in H; inversion H; simpl in H; destruct H; inversion H.
        ++ auto.
Qed.


(*
Lemma renameRule_progres:
  forall left t rl rr rule,
    ~(In (left, rl ++ [inr t] ++ rr) (renameRule rule)).
Proof.
  intros left t rl rr rule contr. destruct rule.
  unfold renameRule in contr. destruct contr; simpl in H.
    - (* inversion H. clear H H1. assert (H' := H2). apply map_length in H2. *)
      induction rl.
      + induction s.
        * simpl in *. inversion H.
        * destruct a. simpl in H. inversion H.
     admit.
      destruct s; [|destruct s0; [|destruct s1]];
      try (destruct R as [L|R]; [|destruct R as [L|R]]; subst; destruct s; destruct s0; simpl in H'; inversion H');
      try (destruct R as [L|R]; [|destruct R as [L|R]]; subst; inversion H2).
    - induction s.
      * inversion H.
      * simpl in H. apply concat_in_lemma in H. destruct H.
        ++ destruct R as [L|R]; [|destruct R as [L|R]]; subst; 
            destruct a; simpl in H; inversion H; simpl in H; destruct H; inversion H.
        ++ auto.
Qed.
*)

(* ----------------------------------------------------------- *)



Lemma lemma_9:
  forall left n0 t0 rules,
    ~ In (left, [inl n0; inr t0]) (flat_map normalizeRule rules).
Proof.
  intros left n0 t0 rules contr. induction rules.
  - simpl in contr. assumption.
  - destruct a. simpl in contr. apply concat_in_lemma in contr. destruct contr.
    + apply renameRule_progress_1_lemma in H. inversion H.
    + apply IHrules. assumption.
Qed.

Lemma lemma_12:
  forall left t0 n0 rules,
    ~ In (left, [inr t0; inl n0]) (flat_map normalizeRule rules).
Proof. 
  intros left n0 t0 rules contr. induction rules.
  - simpl in contr. assumption.
  - destruct a. simpl in contr. apply concat_in_lemma in contr. destruct contr.
    + apply renameRule_progress_2_lemma in H. inversion H.
    + apply IHrules. assumption.
Qed.

Lemma lemma_13:
  forall left t0 t1 rules,
    ~ In (left, [inr t0; inr t1]) (flat_map normalizeRule rules).
Proof.
  intros left n0 t0 rules contr. induction rules.
  - simpl in contr. assumption.
  - destruct a. simpl in contr. apply concat_in_lemma in contr. destruct contr.
    + apply renameRule_progress_3_lemma in H. inversion H.
    + apply IHrules. assumption.
Qed.

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

    apply -> Alg_prop_3. assumption. admit. admit. admit.

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
        admit. (* forall s0 : string, left <> NT ("New_" ++ s0) *)

      eapply derives_step. apply IHderives.  apply -> Alg_prop_2. assumption.
        admit. (* forall s0 : string, left <> NT ("New_" ++ s0) *)
      inversion H5.

      inversion H5. destruct right.
      eapply derives_step. apply IHderives. apply -> Alg_prop_1. assumption.
      inversion H7.

- intros. induction H0.
  + apply derives_refl.
  + assert (H' := H1). apply H in H1. inversion H1.

  destruct right. inversion H3. destruct right. inversion H3. destruct right.
  destruct s0; destruct s4.
  * apply derives_step with (left := left). assumption. apply Alg_prop_3. admit. admit. admit.  assumption.
  * apply Alg_prop_7 in H'. inversion H'.
  * apply Alg_prop_8 in H'. inversion H'.
  
  * apply Alg_prop_9 in H'. inversion H'.
  * inversion H3.
  * inversion H3. destruct right. inversion H5.
  destruct right.
  apply derives_step with (left := left). assumption.

  apply <- Alg_prop_2. assumption.
    admit. (* forall s0 : string, left <> NT ("New_" ++ s0) *)
  inversion H5.
  inversion H5. destruct right. apply derives_step with (left := left). assumption.

  apply <- Alg_prop_1. assumption.
  inversion H7.
Admitted.
