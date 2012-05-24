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
  | exp_err  : exp -> exp
  | exp_catch : exp -> exp -> exp
  | exp_label : atom -> exp -> exp
  | exp_break : atom -> exp -> exp.

Fixpoint open_rec (k : nat) (u : exp) (e : exp) { struct e } := match e with
  | exp_bvar n    => if beq_nat k n then u else e
  | exp_abs  e    => exp_abs (open_rec (S k) u e)
  | exp_app e1 e2 => exp_app (open_rec k u e1) (open_rec k u e2)
  | exp_err e     => exp_err (open_rec k u e)
  | exp_catch e1 e2 => exp_catch (open_rec k u e1) (open_rec (S k) u e2)
  | exp_label x e  => exp_label x (open_rec k u e)
  | exp_break x e => exp_break x (open_rec k u e)
end.

Definition open := open_rec 0.

Inductive lc' : nat -> exp -> Prop :=
  | lc_bvar : forall k n, k < n -> lc' n (exp_bvar k)
  | lc_abs  : forall n e,
      lc' (S n) e -> lc' n (exp_abs e)
  | lc_app  : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_app e1 e2)
  | lc_err  : forall n e, lc' n e -> lc' n (exp_err e)
  | lc_catch : forall n e1 e2,
      lc' n e1 ->
      lc' (S n) e2 ->
      lc' n (exp_catch e1 e2)
  | lc_label : forall n x e,
      lc' n e ->
      lc' n (exp_label x e)
  | lc_break : forall n x e,
      lc' n e ->
      lc' n (exp_break x e).

Definition lc := lc' 0.

Inductive val : exp -> Prop :=
  | val_abs : forall e, lc (exp_abs e) -> val (exp_abs e).

Inductive val' : exp -> Prop :=
  | val'_val : forall v, val v -> val' v
  | val'_err : forall v, val v -> val' (exp_err v)
  | val'_break : forall x v, val v -> val' (exp_break x v).

Inductive E : Set :=
  | E_hole  : E
  | E_app_1 : E -> exp -> E
  | E_app_2 : exp -> E -> E
  | E_err   : E -> E
  | E_catch : E -> exp -> E
  | E_label : atom -> E -> E
  | E_break : atom -> E -> E.

Inductive F : exp -> exp -> Prop :=
  | F_app_1 : forall e1 e2,
      lc e1 ->
      lc e2 ->
      F (exp_app e1 e2) e1
  | F_app_2 : forall v1 e2,
      val v1 ->
      F (exp_app v1 e2) e2
  | F_err : forall e,
      lc e ->
      F (exp_err e) e
  | F_label : forall x e,
      lc e ->
      F (exp_label x e) e
  | F_break : forall x e,
      lc e ->
      F (exp_break x e) e.

Inductive G : exp -> exp -> Prop :=
  | G_app_1 : forall e1 e2,
      lc e1 ->
      lc e2 ->
      G (exp_app e1 e2) e1
  | G_app_2 : forall v1 e2,
      val v1 ->
      G (exp_app v1 e2) e2
  | G_err : forall e,
      lc e ->
      G (exp_err e) e
  | G_break : forall x e,
      lc e ->
      G (exp_break x e) e
  | G_catch : forall e1 e2,
      lc e1 ->
      lc' 1 e2 ->
      G (exp_catch e1 e2) e1.

Inductive red :  exp -> exp -> Prop := 
  | red_app  : forall e v, 
      val v -> red (exp_app (exp_abs e) v) (open v e)
  | red_err_bubble : forall e v,
      F e (exp_err v) ->
      red e (exp_err v)
  | red_uncatch : forall v e,
      val v ->
      red (exp_catch v e) v
  | red_catch : forall v e,
      val v ->
      red (exp_catch (exp_err v) e) (open v e)
  | red_unlabel : forall x v,
      red (exp_label x v) v
  | red_label_match : forall x v,
      val v ->
      red (exp_label x (exp_break x v)) v
  | red_rebreak : forall x y v,
      val v ->
      x <> y ->
      red (exp_label x (exp_break y v)) (exp_break y v)
  | red_break_bubble : forall x e v,
      val v ->
      G e (exp_break x v) ->
      red e (exp_break x v).

Inductive ae : exp -> Prop :=
  | ae_app   : forall e1 e2, val e1 -> val e2 -> ae (exp_app e1 e2)
  | ae_err   : forall e v,
      val v ->
      F e (exp_err v) ->
      ae e
  | ae_uncatch : forall v e,
      val v ->
      lc' 1 e ->
      ae (exp_catch v e)
  | ae_catch : forall v e,
      val v ->
      lc' 1 e ->
      ae (exp_catch (exp_err v) e)
  | ae_unlabel : forall x v,
      val v -> 
      ae (exp_label x v)
  | ae_label_match_and_mismatch : forall x y v,
      val v ->
      ae (exp_label x (exp_break y v))
  | ae_break : forall e x v,
      val v ->
      G e (exp_break x v) ->
      ae e.

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
      cxt (exp_err e) (E_err E) ae
  | cxt_catch : forall e1 e2 E ae,
      cxt e1 E ae ->
      cxt (exp_catch e1 e2) (E_catch E e2) ae
  | cxt_label : forall E ae x e,
      cxt e E ae ->
      cxt (exp_label x e) (E_label x E) ae
  | cxt_break : forall E ae x e,
      cxt e E ae ->
      cxt (exp_break x e) (E_break x E) ae.

Fixpoint plug (e : exp) (cxt : E) := match cxt with
  | E_hole           => e
  | E_app_1 cxt e2   => exp_app (plug e cxt) e2
  | E_app_2 v cxt    => exp_app v (plug e cxt)
  | E_err cxt        => exp_err (plug e cxt)
  | E_catch cxt e2   => exp_catch (plug e cxt) e2
  | E_label x cxt    => exp_label x (plug e cxt)
  | E_break x cxt    => exp_break x (plug e cxt)
end.

Inductive step : exp -> exp -> Prop :=
  | step_red : forall e E ae e',
      lc e ->
      cxt e E ae ->
      red ae e' ->
      step e (plug e' E)
  | step_break : forall x v,
      val v ->
      step (exp_break x v) (exp_err v).

End Definitions.

Hint Constructors cxt ae E val exp val lc' red step val' F G.
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
  | [ Hval : val' ?e1
      |- val' ?e2 \/ (exists E' : E, exists e' : exp, cxt ?e2 E' e') ]
    => let E0 := fresh "E" in
       let e0 := fresh "e" in
       let cxt := fresh "cxt" in
       (inversion Hval; subst; eauto 6; right; eauto 6; destruct Hval as [E0 [e0 cxt]]; eauto 6)
  | [ IH: exists E' : E, exists ae : exp, cxt ?e E' ae
      |- _ ]
    => let E0 := fresh "E" in
       let e0 := fresh "e" in
       let cxt := fresh "cxt" in
       destruct IH as [E0 [e0 cxt]]; eauto 6
end.

Ltac solve_decomp := match goal with
  | [ IH : val' ?e2 \/ (exists E' : E, exists e' : exp, cxt ?e2 E' e') |- _]
    => (destruct IH;  solve_decomp')
  | [ |- _ ] => fail "flasd"
end.

Ltac clean_decomp := repeat match goal with
  | [ IH : 0 = 0 -> ?exp |- _ ]
    => let H := fresh IH in
       (assert exp as H by (apply IH; reflexivity); clear IH)
  | [ IH : 1 = 0 -> _ |- _ ]
    => clear IH
end.

Ltac invert_val' := repeat match goal with
  | [ IH : val' ?e |- _ ]
    => (inversion IH; clear IH)
end.

Ltac invert_val := repeat match goal with
  | [ IH : val ?e |- _ ]
    => (inversion IH; clear IH)
end.

Lemma decomp : forall e,
  lc e -> 
  val' e \/ (exists E, exists e', cxt e E e').
Proof with eauto 6.
intros.
unfold lc in H.
remember 0. 
induction H; intros; subst; clean_decomp; try solve_decomp.
(* bvar *)
inversion H.
(* abs *)
left...
(* app *)
destruct IHlc'0; destruct IHlc'2.
  invert_val'; subst; right...
  solve_decomp'.
  invert_val'; subst; right; solve_decomp'.
  solve_decomp'.
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
  inversion H; subst...
  inversion H0...
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
Proof with auto using lc_val.
  intros. 
  inversion H...
  inversion H1...
  inversion H1...
Qed.

Hint Resolve lc_active lc_val.

Lemma lc_ascend : forall k k' e, k' >= k -> lc' k e -> lc' k' e.
Proof with auto with arith.
intros.
generalize dependent k'.
induction H0; intros...
apply lc_bvar. omega.
Qed.

Lemma lc_open : forall k e u,
  lc' (S k) e ->
  lc' 0 u ->
  lc' k (open_rec k u e).
Proof with try solve [ auto with arith | omega ].
intros.
generalize dependent k.
induction e; intros; try (simpl; inversion H; subst; eauto).
assert (k >= n \/ k < n) as Hkn...
destruct Hkn.
  assert ({ k = n } + { k <> n }) as Hkn'...
  destruct Hkn'.
    assert (beq_nat k n = true). rewrite -> beq_nat_true_iff...
    rewrite -> H2. 
    apply lc_ascend with (k := 0) (k' := k)...
    assert (beq_nat k n = false).  rewrite -> beq_nat_false_iff...
    rewrite -> H2.
    assert (n < k)...
assert (beq_nat k n = false). rewrite -> beq_nat_false_iff...
rewrite -> H2.
apply lc_bvar.
inversion H...
Qed.

Hint Resolve lc_ascend lc_open.

Lemma lc_red : forall ae e,
  lc ae ->
  red ae e ->
  lc e.
Proof with (unfold lc in *; unfold open in *; try solve [ auto | inversion H; auto ]).
intros.
destruct H0...
(* app *)
inversion H... inversion H4...
(* err *)
inversion H0; subst...
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
apply lc_plug with (e' := e') (E := E0) (ae := ae0) (e := e)...
apply lc_red with (ae := ae0)...
apply cxt_lc with (E := E0) (e := e)...
Qed.

End LC.