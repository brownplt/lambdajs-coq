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

Module LC (Import Atom : ATOM).

Definition atom := Atom.atom. (* free variables *)

Section Definitions.

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

Inductive E : Set :=
  | E_hole  : E
  | E_app_1 : E -> exp -> E
  | E_app_2 : exp -> E -> E
  | E_err   : E -> E.

Inductive red :  exp -> exp -> Prop := 
  | red_app  : forall e v, 
      val v -> red (exp_app (exp_abs e) v) (open v e)
  | red_app_err1 : forall v1 e2,
      val v1 -> red (exp_app (exp_err v1) e2) (exp_err v1)
  | red_app_err2 : forall v1 v2,
      val v1 -> val v2 -> red (exp_app v1 (exp_err v2)) (exp_err v2)
  | red_err_err : forall v,
      val v-> red (exp_err (exp_err v)) (exp_err v).

Inductive ae : exp -> Prop :=
  | ae_app   : forall e1 e2, val e1 -> val e2 -> ae (exp_app e1 e2)
  | ae_app_err1 : forall v1 e2, val v1 -> lc e2 -> ae (exp_app (exp_err v1) e2)
  | ae_app_err2 : forall v1 v2, 
      val v1 -> val v2 -> ae (exp_app v1 (exp_err v2))
  | ae_err_err  : forall v,
      val v -> ae (exp_err (exp_err v)).

Inductive cxt : exp -> E -> exp -> Prop :=
  | cxt_hole : forall e,
      ae e ->
      cxt e E_hole e
  | cxt_app_1 : forall E e1 e2 e',
      cxt e1 E e' ->
      cxt (exp_app e1 e2) (E_app_1 E e2) e'
  | cxt_app_2 : forall E v e e',
      cxt e E e' ->
      val v ->
      cxt (exp_app v e) (E_app_2 v E) e'
  | cxt_err : forall e E ae,
      cxt e E ae ->
      cxt (exp_err e) (E_err E) ae.

Fixpoint plug (e : exp) (cxt : E) := match cxt with
  | E_hole           => e
  | E_app_1 cxt e2   => exp_app (plug e cxt) e2
  | E_app_2 v cxt    => exp_app v (plug e cxt)
  | E_err cxt        => exp_err (plug e cxt)
end.

Inductive step : exp -> exp -> Prop :=
  | step_red : forall e E ae e',
      lc e ->
      cxt e E ae ->
      red ae e' ->
      step e (plug e' E).

End Definitions.

Hint Constructors cxt ae E val exp val lc' red step val'.
Hint Unfold open lc.

Lemma plug_ok : forall e E e',
  cxt e E e' -> plug e' E = e.
Proof.
  intros.
  induction H; simpl; try (auto || rewrite -> IHcxt; auto).
Qed.

Lemma cxt_lc : forall E e ae,
  lc e ->
  cxt e E ae ->
  lc ae.
Proof. intros. induction H0; inversion H; eauto. Qed.

Ltac destruct_decomp e := match goal with
  |  [ H : exists E : E, exists ae : exp, cxt e E ae |- _ ] =>
       destruct H as [E [ae H]]
  | _ => fail
end.

Ltac solve_decomp' := match goal with
  | [ H1 : lc' 0 ?e,
      IHe : val ?e \/ 
            (exists E' : E, exists ae : exp, cxt ?e E' ae)
      |- val ?exp \/ (exists E0 : E, exists ae : exp, cxt ?exp E0 ae) ]
    => (destruct IHe; right; eauto; destruct_decomp e; eauto)
  | [ |- _] => fail "solve_decomp'"
end.

Ltac solve_decomp := match goal with
  | [ IH : 0 = 0 -> _ |- _ ]
    => (remember (IH (eq_refl 0)); solve_decomp')
  | [ |- _ ] => fail "flasd"
end.

Lemma decomp : forall e,
  lc e -> 
  val' e \/ (exists E, exists e', cxt e E e').
Proof with eauto.
intros.
unfold lc in H.
remember 0.
induction H; intros; subst.
(* bvar *)
inversion H.
(* abs *)
left...
(* app *)
destruct IHlc'1; try reflexivity. destruct IHlc'2; try reflexivity.
  inversion H1; subst. 
  inversion H3; subst.
  inversion H2; subst.
  right...
  right...
  right...
  inversion H1; subst.
  destruct H2 as [E [e' cxt]].
  right...
  right...
  destruct H1 as [E [e' cxt]].
  right...
(* err *)
destruct IHlc'.
  reflexivity.
  inversion H0; subst.
  eauto.
  right...
  destruct H0 as [E [e' cxt]]...
Qed.

Hint Resolve cxt_lc.

Lemma cxt_ae : forall E e e',
  cxt e E e' ->
  ae e'.
Proof.
  intros. induction H; auto.
Qed.

Lemma red_ae : forall e,
  ae e ->
  exists e', red e e'.
Proof with eauto.
  intros.
  inversion H; subst.
    inversion H0.
    exists (open e2 e)...
    exists (exp_err v1)...
    exists (exp_err v2)...
    exists (exp_err v)...
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
destruct_decomp e.
remember (red_ae (cxt_ae H)) as H1.
destruct H1 as [e'' Hred].
right...
Qed.

Ltac solve_lc_plug := match goal with
  | [ IHdecompose : lc' 0 ?e -> lc' 0 (plug ?e' ?E),
      H : lc' 0 ?e
      |- context [plug ?e' ?E] ]
    => (apply IHdecompose in H; auto)
end.

Lemma lc_plug : forall E ae e e',
  lc e ->
  lc e' ->
  cxt e E ae ->
  lc (plug e' E).
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
apply lc_plug with (e' := e') (E := E0) (ae := ae0) (e := e)...
apply lc_red with (ae := ae0)...
apply cxt_lc with (E := E0) (e := e)...
Qed.

End LC.