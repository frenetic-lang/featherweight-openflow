Set Implicit Arguments.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.EqNat.

Local Open Scope bool_scope.

Definition pk : Set := (nat * nat * nat * nat) %type.

Inductive trace : Set := 
| tr_single : pk -> trace
| tr_cons : pk -> trace -> trace.

Inductive hdr :=
| sw : hdr
| pt : hdr
| src : hdr
| dst : hdr.

Definition val := nat.

Definition upd (h : hdr) (v : val) (p : pk) : pk :=
  match (h, p) with
    | (sw, (_, v2, v3, v4)) => (v, v2, v3, v4)
    | (pt, (v1, _, v3, v4)) => (v1, v, v3, v4)
    | (src, (v1, v2, _, v4)) => (v1, v2, v, v4)
    | (dst, (v1, v2, v3, _)) => (v1, v2, v3, v)
  end.

Definition test (h : hdr) (v : val) (p : pk) : bool :=
  match (h, p) with
    | (sw, (v1, v2, v3, v4)) => beq_nat v v1
    | (pt, (v1, v2, v3, v4)) => beq_nat v v2
    | (src, (v1, v2, v3, v4)) => beq_nat v v3
    | (dst, (v1, v2, v3, v4)) => beq_nat v v4
  end.

Definition head (tr : trace) : pk :=
  match tr with
    | tr_single pk => pk
    | tr_cons pk _ => pk
  end.

Definition replace_head (pk : pk) (tr : trace) : trace :=
  match tr with
    | tr_single _ => tr_single pk
    | tr_cons _ tr' => tr_cons pk tr'
  end.

Axiom hdr_eqdec : forall (h1 h2 : hdr), { h1 = h2 } + { h1 <> h2 }.
Axiom val_eqdec : forall (v1 v2 : val), { v1 = v2 } + { v1 <> v2 }.

Create HintDb pkt.

Lemma head_replace_head : forall pk a, head (replace_head pk a) = pk.
Proof with auto.
  intros.
  destruct a...
Qed.

Lemma replace_head2 : 
  forall pk1 pk2 a, 
    replace_head pk1 (replace_head pk2 a) = replace_head pk1 a.
Proof with auto.
  intros.
  destruct a...
Qed.

Hint Rewrite head_replace_head replace_head2 : pkt.

Lemma test_upd_true : forall h n pk, test h n (upd h n pk) = true.
Proof with auto.
  intros.
  destruct pk0 as [[[sw pt] src] dst].
  unfold test.
  unfold upd.
  destruct h; auto; rewrite <- beq_nat_refl...
Qed.

Lemma test_upd_ignore :
  forall h1 h2 m n pk,
    h1 <> h2 ->
    test h2 n (upd h1 m pk) = test h2 n pk.
Proof with auto.
  intros.
  destruct pk0 as [[[sw pt] src] dst].
  unfold not in H.
  destruct h1; destruct h2; try solve[contradiction H; auto];
  unfold upd;
  unfold test...
Qed.

Lemma test_upd_0 :
  forall h m n pk,
    m <> n ->
    test h m (upd h n pk) = false.
Proof with auto.
  intros.
  destruct pk0 as [[[sw pt] src] dst].
  destruct h; unfold upd; unfold test;
  rewrite -> beq_nat_false_iff...
Qed.

Lemma test_true_diff :
  forall h m n pk,
    true = test h m pk ->
    true = test h n pk ->
    m = n.
Proof with auto.
  intros.
  destruct pk0 as [[[sw pt] src] dst].
  unfold test in *.
  symmetry in H.
  symmetry in H0.
  destruct h; rewrite -> beq_nat_true_iff in *; subst...
Qed.

Lemma upd_upd_compress : 
  forall h m n pk,
    upd h m (upd h n pk) = upd h m pk.
Proof with auto.
  intros.
  destruct pk0 as [[[sw pt] src] dst].
  unfold upd. 
  destruct h; simpl...
Qed.