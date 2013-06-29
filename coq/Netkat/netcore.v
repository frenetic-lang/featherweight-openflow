Set Implicit Arguments.

Require Import kat normalisation rewriting kat_tac.
Require Import rel comparisons.

Require Import Packet.

Local Open Scope bool_scope.

Inductive pred : Type :=
| pr_true
| pr_false
| pr_and : pred -> pred -> pred
| pr_or : pred -> pred -> pred
| pr_not : pred -> pred
| pr_test : hdr -> val -> pred.

Inductive pol : Type :=
| po_id : pol
| po_drop : pol
| po_sum : pol -> pol -> pol
| po_seq : pol -> pol -> pol
| po_star : pol -> pol
| po_pred : pred -> pol
| po_upd : hdr -> val -> pol
| po_upd_obs : hdr -> val -> pol.

Definition test0 h v : dset trace :=
  fun tr => test h v (head tr).

Fixpoint eval_pred (pr : pred) : dset trace  := 
  match pr with
    | pr_and pr1 pr2 => eval_pred pr1 \cap eval_pred pr2
    | pr_or pr1 pr2 => eval_pred pr1 \cup eval_pred pr2
    | pr_true => top
    | pr_false => bot
    | pr_not pr' => ! (eval_pred pr')
    | pr_test h v => test0 h v
  end.

Definition upd0 h v : rel trace trace :=
  fun t1 t2 => replace_head (upd h v (head t1)) t1 = t2.

Definition obs0 h v : rel trace trace :=
  fun t1 t2 => tr_cons (upd h v (head t1)) t1 = t2.

Fixpoint eval_pol (po : pol) : rel trace trace :=
  match po with
    | po_id => 1
    | po_drop => 0
    | po_sum e1 e2 => eval_pol e1 + eval_pol e2
    | po_seq e1 e2 => eval_pol e1 * eval_pol e2
    | po_star e' => (eval_pol e')^*
    | po_pred pr => [eval_pred pr]
    | po_upd h v => upd0 h v
    | po_upd_obs h v => obs0 h v
  end.
  
Coercion po_pred : pred >-> pol.

Reserved Notation "h ~:= n" (at level 48, no associativity).
Reserved Notation "h ^:= n" (at level 48, no associativity).
Reserved Notation "h =? n" (at level 48, no associativity).
Reserved Notation "x ; y" (at level 50, left associativity).

Module KatNotation.

  Notation "h =? n" := (pr_test h n) : kat_scope.
  Notation "h ~:= n" := (po_upd h n) : kat_scope.
  Notation "h ^:= n" := (po_upd_obs h n) : kat_scope.
  Notation "x + y" := (po_sum x y) : kat_scope.
  Notation "x ; y" := (po_seq x y) : kat_scope.
  Notation "x ^*" := (po_star x) : kat_scope.
  Notation "#t" := pr_true : kat_scope.
  Notation "#f" := pr_false : kat_scope.
  Notation "x && y" := (pr_and x y) : kat_scope.
  Notation "x || y" := (pr_or x y) : kat_scope.
  Notation "p ~ q" := (eval_pol p == eval_pol q) (at level 80) : kat_scope.
  Notation "~ p" := (pr_not p).

End KatNotation.

Module Notation.

  Notation "h =? n" := (test0 h n) : netcore_scope.
  Notation "h ~:= n" := (upd0 h n) : netcore_scope.
  Notation "h ^:= n" := (obs0 h n) : netcore_scope.
  Notation "x + y" := (x + y) : netcore_scope.
  Notation "x ; y" := (x * y) : netcore_scope.
  Notation "p ~ q" := 
    (eval_pol p == eval_pol q) (at level 80) : netcore_scope.
  Notation "~ p" := (pr_not p).

End Notation.

Section DomainEquations.

  Variable h h1 h2 : hdr.
  Variable m n : val.

  Import Notation.
  Local Open Scope netcore_scope.

  Hint Unfold rel_dot rel_inj test0 obs0 upd0.
  Lemma upd_compress : (h~:=m) * (h~:=n) == (h~:=n).
  Proof with auto.
    simpl. intros. autounfold. split; intros.
    + destruct H.
      destruct (head a) as [[[sw pt] src] dst].
      subst.
      autorewrite with pkt using simpl...
      rewrite -> upd_upd_compress...
    + destruct (head a) as [[[sw pt] src] dst].
      subst. eexists. reflexivity.
      autorewrite with pkt using simpl...
      rewrite -> upd_upd_compress...
  Qed.

  Lemma upd_comm : h1 <> h2 -> h1~:=m; h2~:=n == h2~:=n; h1~:=m.
  Proof with auto.
    simpl. intros. autounfold. split; intros.
    + destruct H0.
      subst.
      destruct (head a) as [[[sw pt] src] dst].
      unfold not in H.
      destruct h1; destruct h2;
      try solve [contradiction H; trivial |
                 destruct a; eexists; simpl; eauto].
    + intros.
      destruct H0.
      subst.
      destruct (head a) as [[[sw pt] src] dst].
      unfold not in H.
      destruct h1; destruct h2; 
      try solve [contradiction H; trivial |
                 destruct a; eexists; simpl; eauto].
  Qed.

  Lemma upd_test_compress : h~:=n; [h=?n] == h~:=n.
  Proof with eauto.
    simpl. intros. autounfold. split; intros.
    + destruct H. destruct H0. subst.
      trivial.
    + subst. eexists. reflexivity.
      unfold rel_inj.
      split...
      autorewrite with pkt using simpl.
      rewrite -> test_upd_true...
  Qed.

  Lemma upd_test_comm : h1 <> h2 -> h1~:=m; [h2=?n] == [h2=?n]; h1~:=m.
  Proof with eauto.
    simpl. intros. autounfold. split; intros.
    + destruct H0. destruct H1. subst.
      autorewrite with pkt in H2 using (simpl in H2). subst.
      rewrite -> test_upd_ignore in H2...
    + destruct H0. destruct H0. subst.
      eexists. reflexivity.
      split...
      autorewrite with pkt using simpl.
      rewrite -> test_upd_ignore...
  Qed.

  Lemma test_test_zero : m <> n -> [h=?m]; [h=?n] == bot.
  Proof with eauto.
    simpl. intros. autounfold. split; intros.
    + destruct H0 as [a1 [H0 H1] [H2 H3]].
      subst.
      assert (m = n). 
      { eapply test_true_diff... }
      subst...
    + inversion H0.
  Qed.

  Lemma upd_test_zero : m <> n -> h~:=n; [h=?m] == bot.
  Proof with eauto.
    simpl. intros. autounfold. split; intros.
    destruct H0.
    + destruct H1. subst.
      remember (test h m (head a)) as b.
      destruct b.
      - subst.
        autorewrite with pkt in H2 using (simpl in H2)...
        rewrite -> test_upd_0 in H2...
        inversion H2.
      - subst.
        autorewrite with pkt in H2 using (simpl in H2)...
        rewrite -> test_upd_0 in H2...
        inversion H2.
    + inversion H0.
  Qed.

  Lemma obs_test_compress : h^:=n; [h=?n] == h^:=n.
  Proof with eauto.
    simpl. intros. autounfold. split; intros.
    + destruct H as [a1 H [H0 H1]]. subst.
      simpl in H1.
      rewrite -> test_upd_true in H1...
    + subst. eexists. reflexivity.
      split...
      simpl.
      rewrite -> test_upd_true...
  Qed.

  Lemma obs_test_comm : h1 <> h2 -> h1^:=m; [h2=?n] == [h2=?n]; h1^:=m.
  Proof with eauto.
    simpl. intros. autounfold. split; intros.
    + destruct H0 as [tr J [J0 J1]]. subst.
      simpl in J1.
      rewrite -> test_upd_ignore in J1...
    + destruct H0 as [tr [J0 J1] J]. subst.
      eexists...
      split...
      simpl.
      rewrite -> test_upd_ignore...
  Qed.

  Lemma obs_test_zero : m <> n -> h^:=m; [h=?n] == bot.
  Proof with eauto.
    simpl. intros. autounfold. split; intros.
    + destruct H0 as [tr J [J0 J1]]. subst.
      simpl in J1.
      rewrite -> test_upd_0 in J1...
      inversion J1.
    + inversion H0.
  Qed.

  Lemma obs_upd_compress : h^:=m; h~:=n == h^:=n.
  Proof with eauto.
    simpl. intros. autounfold. split; intros.
    + destruct H. subst. simpl.
      rewrite -> upd_upd_compress...
    + subst.
      eexists. reflexivity.
      simpl.
      rewrite -> upd_upd_compress...
  Qed.

End DomainEquations.

Ltac kat_simpl := 
  unfold eval_pol; unfold eval_pred; fold eval_pred; fold eval_pol.
