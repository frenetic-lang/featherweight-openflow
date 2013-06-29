Set Implicit Arguments.

Require Import kat normalisation rewriting kat_tac.
Require Import rel comparisons netcore.
Require Import Packet.
        
  Section Eg.
    Import KatNotation.
    Local Open Scope kat_scope.
    
  Definition topo := sw=?S 0; pt=?2; sw^:=2; pt~:=S 0 +
                     sw=?2; pt~:=S 0; sw^:=S 0; pt~:=2.                        
  Definition fwd := pt=?S 0; pt~:=2 + pt=?2; pt~:=S 0.
  Definition pol1 := 
    sw=?S 0;(pt=?S 0; pt~:=2 + pt=?2; pt~:=S 0) +
    sw=?2;((~src=?10); pt=?S 0; pt~:=2 + pt=?2; pt~:=S 0).

  Lemma trivial_kat : forall  b, po_id + b;b^* ~ b^*.
  Proof.
    intros.
    kat_simpl.
    kat.
  Qed.

  Definition foo :=     sw=?S 0; pt=?S 0; src=?10; (pol1; topo)^* ; sw=?2;pt=?2 ~ po_drop.


  End Eg.

  Import Notation.
  Local Open Scope netcore_scope.


  Lemma comm_tests : 
    forall (e : rel trace trace) h1 h2 v1 v2,
      [h1 =? v1]; [h2 =? v2] == [h2 =? v2]; [h1 =? v1].
  Proof. intros. kat. Qed.

  Lemma test_order_sw_src : 
    forall (e : rel trace trace) m n, 
      e; [src =? m]; [sw =? n] == e; [sw =? n]; [src =? m].
  Proof. intros. kat. Qed.

  Lemma test_order_sw_pt : 
    forall (e : rel trace trace) m n, 
      e; [pt =? m]; [sw =? n] == e; [sw =? n]; [pt =? m].
  Proof. intros. kat. Qed.
  
  Lemma test_order_pt_src :
    forall (e : rel trace trace) m n, 
      e; [src =? m]; [pt =? n] == e; [pt =? n]; [src =? m].
  Proof. intros. kat. Qed.

  Lemma trace_assoc : 
    forall (e1 e2 e3 : rel trace trace),
      e1; e2; e3 == e1; (e2; e3).
  Proof. kat. Qed.      

  Lemma line_test_test_zero :
    forall (e : rel trace trace) h m n, 
      m <> n ->
      e; [h =? m]; [h =? n] == 0.
  Proof. 
    intros.
    rewrite -> trace_assoc.
    rewrite -> test_test_zero; auto.
    kat.
  Qed.

  Lemma line_upd_test_zero :
    forall (e : rel trace trace) h m n, 
      m <> n ->
      e; h ~:= m; [h =? n] == 0.
  Proof with auto.
    intros.
    rewrite -> trace_assoc. rewrite -> upd_test_zero...
    kat.
  Qed.

  Lemma line_test_compress :
    forall (e : rel trace trace) h n,
      e; [h =? n]; [h =? n] == e; [h =? n].
  Proof.
    kat.
  Qed.

  Hint Rewrite
       test_order_sw_pt
       test_order_sw_src
       test_order_pt_src
       line_test_compress
  : netcore.
    
  Lemma firewall_ok1 : foo.
  Proof with auto.
    intros.
    unfold foo.
    unfold pol1.
    unfold topo.
    kat_simpl.
    ra_normalise.
    rewrite -> str_unfold_l.
    ra_normalise.
    autorewrite with netcore using idtac.
    rewrite -> test_test_zero.
    ra_normalise.
    rewrite -> (@line_test_test_zero _ pt (S O) 2).
    ra_normalise.
    rewrite -> (@line_upd_test_zero _ pt (S O) 2).
    ra_normalise.
  Admitted.

