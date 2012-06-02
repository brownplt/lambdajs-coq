(* 
 * An encoding of the untyped lambda calculus with numbers.
 *
 * Authors: 
 *   Arjun Guha <arjun@cs.brown.edu>
 *   Benjamin Lerner <blerner@cs.brown.edu>
 *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Omega.
Set Implicit Arguments.

Module Type ATOM.

  Parameter atom : Set.

End ATOM.

Module CBV_Defs (Import Atom : ATOM).

Definition atom := Atom.atom. (* free variables *)

Inductive exp : Set :=
  | exp_bvar : nat -> exp (* bound variables as de Brujin indices *)
  | exp_abs  : exp -> exp
  | exp_app  : exp -> exp -> exp
  | exp_err  : exp -> exp.

Fixpoint open_rec (k : nat) (u : exp) (e : exp) { struct e } := match e with
  | exp_bvar n    => if beq_nat k n then u else e
  | exp_abs  e    => exp_abs (open_rec (S k) u e)
  | exp_app e1 e2 => exp_app (open_rec k u e1) (open_rec k u e2)
  | exp_err e     => exp_err (open_rec k u e)
end.

Definition open := open_rec 0.

Inductive lc' : nat -> exp -> Prop :=
  | lc_bvar : forall k n, k < n -> lc' n (exp_bvar k)
  | lc_abs  : forall n e,
      lc' (S n) e -> lc' n (exp_abs e)
  | lc_app  : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_app e1 e2)
  | lc_err  : forall n e, lc' n e -> lc' n (exp_err e).

Definition lc := lc' 0.

Inductive val : exp -> Prop :=
  | val_abs : forall e, lc (exp_abs e) -> val (exp_abs e).

Inductive val' : exp -> Prop :=
  | val'_val : forall v, val v -> val' v
  | val'_err : forall v, val v -> val' (exp_err v).

Inductive C : Set :=
  | C_hole  : C
  | C_app_1 : C -> exp -> C
  | C_app_2 : exp -> C -> C
  | C_err   : C -> C.

Inductive red :  exp -> exp -> Prop := 
  | red_app  : forall e v, 
      val v -> red (exp_app (exp_abs e) v) (open v e)
  | red_app_err1 : forall v1 e2,
      val v1 -> red (exp_app (exp_err v1) e2) (exp_err v1)
  | red_app_err2 : forall v1 v2,
      val v1 -> val v2 -> red (exp_app v1 (exp_err v2)) (exp_err v2)
  | red_err_err : forall v,
      val v-> red (exp_err (exp_err v)) (exp_err v).

Inductive E : exp -> C -> exp -> Prop :=
  | E_hole : forall e,
      E e C_hole e
  | E_app_1 : forall C e1 e2 e',
      E e1 C e' ->
      E (exp_app e1 e2) (C_app_1 C e2) e'
  | E_app_2 : forall C v e e',
      E e C e' ->
      val v ->
      E (exp_app v e) (C_app_2 v C) e'
  | E_err : forall e C ae,
      E e C ae ->
      E (exp_err e) (C_err C) ae.

Fixpoint plug (e : exp) (cxt : C) := match cxt with
  | C_hole           => e
  | C_app_1 cxt e2   => exp_app (plug e cxt) e2
  | C_app_2 v cxt    => exp_app v (plug e cxt)
  | C_err cxt        => exp_err (plug e cxt)
end.

Inductive step : exp -> exp -> Prop :=
  | step_red : forall e C ae e',
      lc e ->
      E e C ae ->
      red ae e' ->
      step e (plug e' C).

Hint Constructors C E val exp val lc' red step val'.
Hint Unfold open lc.

End CBV_Defs.

Module CBV_Proofs (Import Atom : ATOM).

Module Import Defs := CBV_Defs (Atom).

Inductive ae : exp -> Prop :=
  | ae_app   : forall e1 e2, val e1 -> val e2 -> ae (exp_app e1 e2)
  | ae_app_err1 : forall v1 e2, val v1 -> lc e2 -> ae (exp_app (exp_err v1) e2)
  | ae_app_err2 : forall v1 v2, 
      val v1 -> val v2 -> ae (exp_app v1 (exp_err v2))
  | ae_err_err  : forall v,
      val v -> ae (exp_err (exp_err v)).

Hint Constructors ae.

Lemma plug_ok : forall e C e',
  E e C e' -> plug e' C = e.
Proof.
  intros.
  induction H; simpl; try (auto || rewrite -> IHE; auto).
Qed.

Lemma E_lc : forall C e ae,
  lc e ->
  E e C ae ->
  lc ae.
Proof. intros. induction H0; inversion H; eauto. Qed.

Ltac destruct_decomp e := match goal with
  |  [ H : exists C : C, exists e' : exp, E e C e' /\ ae e' |- _ ] =>
       destruct H as [C' [e' [H Hae]]]
  | _ => fail
end.

Ltac solve_decomp' := match goal with
  | [ H1 : lc' 0 ?e,
      IHe : val ?e \/ 
            (exists C' : C, exists ae : exp, E ?e C' ae)
      |- val ?exp \/ (exists C0 : C, exists ae : exp, E ?exp C0 ae) ]
    => (destruct IHe; right; eauto; destruct_decomp e; eauto)
  | [ |- _] => fail "solve_decomp'"
end.

Ltac clean_decomp := repeat match goal with
  | [ IH : 0 = 0 -> ?H |- _ ] => assert H by (apply IH; reflexivity); clear IH
  | [ IH : 1 = 0 -> _ |- _ ] => clear IH
end.

Ltac decomp_cases e := match goal with
  |  [ H : val' e \/ (exists C : C, exists e' : exp, E e C e' /\ ae e') |- _ ] =>
     let Hval := fresh "Hval" in
     let C' := fresh "C" in
     let e' := fresh "e" in
     let Hae := fresh "Hae" in
     destruct H as [Hval | [C' [e' [H Hae]]]]; [ inversion Hval; subst | idtac ]
  | _ => fail
end.

Lemma decomp : forall e,
  lc e -> 
  val' e \/ (exists C, exists e', E e C e' /\ ae e').
Proof with eauto.
intros.
unfold lc in H.
remember 0.
induction H; intros; subst; clean_decomp.
(* bvar *)
inversion H.
(* abs *)
left...
(* app *)
decomp_cases e1; decomp_cases e2; eauto 6.
(* err *)
decomp_cases e1; eauto 6.
Qed.

Hint Resolve E_lc.

Lemma red_ae : forall e,
  ae e ->
  exists e', red e e'.
Proof with eauto.
  intros.
  inversion H; subst; try solve [ inversion H0; eapply ex_intro; eauto ].
Qed.
   
Lemma progress : forall e,
  lc e ->
  val' e \/ (exists e', step e e').
Proof with eauto.
  intros.
  remember H as HLC.
  clear HeqHLC.
  apply decomp in H.
  destruct H...
  destruct H as [C' [e' [HE Hae]]].
  apply red_ae in Hae.
  destruct Hae as [e2 Hred]...
Qed.

Ltac solve_lc_plug := match goal with
  | [ IHdecompose : lc' 0 ?e -> lc' 0 (plug ?e' ?C),
      H : lc' 0 ?e
      |- context [plug ?e' ?C] ]
    => (apply IHdecompose in H; auto)
end.

Lemma lc_plug : forall C ae e e',
  lc e ->
  lc e' ->
  E e C ae ->
  lc (plug e' C).
Proof.
intros.
induction H1; first [ inversion H; subst; simpl; unfold lc in *; solve_lc_plug | auto ].
Qed.

Hint Resolve lc_plug.

Lemma lc_val : forall v,
  val v -> lc' 0 v.
Proof with auto.
intros. inversion H... Qed.

Lemma lc_active : forall e,
  ae e -> lc e.
Proof. intros. unfold lc. inversion H; auto using lc_val. Qed.

Hint Resolve lc_active lc_val.

Lemma lc_ascend : forall k k' e, k' >= k -> lc' k e -> lc' k' e.
Proof with auto.
  intros.
  generalize dependent k'.
  induction H0...
  intros. apply lc_bvar. omega.
  intros. apply lc_abs. apply IHlc'. omega.
Qed.

Lemma lc_open : forall k e u,
  lc' (S k) e ->
  lc' 0 u ->
  lc' k (open_rec k u e).
Proof with auto.
  intros.
  generalize dependent k.
  induction e; intros; try (simpl; inversion H; subst; eauto).
  assert (k >= n \/ k < n). apply le_or_lt.
  destruct H1.
  assert ({ k = n } + { k <> n }). decide equality.
  destruct H2.
  assert (beq_nat k n = true). rewrite -> beq_nat_true_iff...
  rewrite -> H2.  assert (k >= 0). omega.
    apply lc_ascend with (k := 0) (k' := k)...
  assert (beq_nat k n = false).  rewrite -> beq_nat_false_iff...
  rewrite -> H2.
  assert (n < k). omega. auto...
  (* k < n *)
  assert (beq_nat k n = false).  rewrite -> beq_nat_false_iff... omega.
  rewrite -> H2. apply lc_bvar.
  clear H2.
  inversion H; subst.
  assert False. omega.
  inversion H2.
Qed.

Hint Resolve lc_ascend lc_open.

Lemma lc_red : forall ae e,
  lc ae ->
  red ae e ->
  lc e.
Proof with auto.
  intros.
  destruct H0...
  (* app *)
  unfold lc in *.
  inversion H; subst.
  unfold open.
  inversion H4; subst...
Qed.

Hint Resolve lc_red.

Lemma preservation : forall e1 e2,
  lc e1 ->
  step e1 e2 ->
  lc e2.
Proof with auto.
  intros.
  unfold lc in *.
  destruct H0...
  (*    : forall (E : E) (ae e e' : exp),
           lc e -> lc e' -> cxt e E ae -> lc (plug e' E) *)
  apply lc_plug with (e' := e') (C := C0) (ae := ae0) (e := e)...
  apply lc_red with (ae := ae0)...
  apply E_lc with (C := C0) (e := e)...
Qed.

End CBV_Proofs.