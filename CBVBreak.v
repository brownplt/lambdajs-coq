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
Require Import Coq.Structures.Orders.
Require Import Coq.Arith.NatOrderedType.
Require Import Coq.MSets.MSetList.
Require Import Omega.
Set Implicit Arguments.

Module Type ATOM.

  Parameter atom : Set.
  Declare Module Atom_as_OT : UsualOrderedType with Definition t := atom.

End ATOM.

Module LC (Import Atom : ATOM).

Module Atoms := Coq.MSets.MSetList.Make (Atom.Atom_as_OT).

Definition atom := Atom.atom. (* free variables *)

Section Definitions.

Inductive exp : Set :=
  | exp_bvar : nat -> exp (* bound variables as de Brujin indices *)
  | exp_abs  : exp -> exp
  | exp_app  : exp -> exp -> exp
  | exp_err  : exp
  | exp_label : atom -> exp -> exp
  | exp_break : atom -> exp -> exp.

(* open_rec is the analogue of substitution for de Brujin indices.
  open_rec k u e replaces index k with u in e. *)
Fixpoint open_rec (k : nat) (u : exp) (e : exp) { struct e } := match e with
  | exp_bvar n    => if beq_nat k n then u else e
  | exp_abs  e    => exp_abs (open_rec (S k) u e)
  | exp_app e1 e2 => exp_app (open_rec k u e1) (open_rec k u e2)
  | exp_err       => e
  | exp_label x e => exp_label x (open_rec k u e)
  | exp_break x e => exp_break x (open_rec k u e)
end.

Definition open e u := open_rec 0 u e.

(* locally closed : all de Brujin indices are bound *)
Inductive lc' : nat -> exp -> Prop :=
  | lc_bvar : forall k n, k < n -> lc' n (exp_bvar k)
  | lc_abs  : forall n e,
      lc' (S n) e -> lc' n (exp_abs e)
  | lc_app  : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_app e1 e2)
  | lc_err   : forall n, lc' n exp_err
  | lc_label : forall n x e, lc' n e -> lc' n (exp_label x e)
  | lc_break : forall n x e, lc' n e -> lc' n (exp_break x e).

Definition lc e := lc' 0 e.

Inductive val : exp -> Prop :=
  | val_abs : forall e, lc (exp_abs e) -> val (exp_abs e).

Inductive E : Set :=
  | E_hole  : E
  | E_app_1 : E -> exp -> E
  | E_app_2 : forall (v : exp), val v -> E -> E
  | E_label : atom -> E -> E
  | E_break : atom -> E -> E.

Inductive pot_redex : exp -> Prop :=
  | redex_app  : forall e1 e2, val e1 -> val e2 -> pot_redex (exp_app e1 e2)
  | redex_err  : pot_redex exp_err
  | redex_label : forall x v, val v -> pot_redex (exp_label x v)
  | redex_break : forall x v, val v -> pot_redex (exp_break x v).

Inductive decompose : exp -> E -> exp -> Prop :=
  | cxt_hole : forall e,
      pot_redex e ->
      decompose e E_hole e
  | cxt_app_1 : forall E e1 e2 e',
      decompose e1 E e' ->
      decompose (exp_app e1 e2) (E_app_1 E e2) e'
  | cxt_app_2 : forall E v e (p : val v) e',
      decompose e E e' ->
      decompose (exp_app v e) (E_app_2 p E) e'
  | cxt_break : forall x e E ae,
      decompose e E ae ->
      decompose (exp_break x e) (E_break x E) ae
  | cxt_label : forall x e E ae,
      decompose e E ae ->
      decompose (exp_label x e) (E_label x E) ae.

Inductive decompose1 : exp -> E -> exp -> Prop :=
  | cxt1_hole : forall e,
      pot_redex e ->
      decompose1 e E_hole e
  | cxt1_app_1 : forall e1 e2,
      decompose1 (exp_app e1 e2) (E_app_1 E_hole e2) e1
  | cxt1_app_2 : forall v e (p : val v),
      decompose1 (exp_app v e) (E_app_2 p E_hole) e
  | cxt1_break : forall x e,
      decompose1 (exp_break x e) (E_break x E_hole) e.

Fixpoint plug (e : exp) (cxt : E) := match cxt with
  | E_hole => e
  | E_app_1 cxt e2 => exp_app (plug e cxt) e2
  | E_app_2 v pf cxt => exp_app v (plug e cxt)
  | E_label x cxt => exp_label x (plug e cxt)
  | E_break x cxt => exp_break x (plug e cxt)
end.

Inductive contract :  exp -> exp -> Prop := 
  | contract_app  : forall e v, 
      val v -> contract (exp_app (exp_abs e) v) (open e v)
  | contract_label : forall x v,
      val v -> contract (exp_label x v) v
  | contract_break_bubble : forall x v E e,
    decompose1 e E (exp_break x v) ->
    contract e (exp_break x v)
  | contract_break_match : forall x v,
    contract (exp_label x (exp_break x v)) v
  | contract_break_mismatch : forall x y v,
    x <> y ->
    contract (exp_label x (exp_break y v)) (exp_break y v).

Inductive step : exp -> exp -> Prop :=
  (* Slightly strange: exp_err -> exp_err -> exp_err -> ... *)
  | step_err : forall e E,
    lc e ->
    decompose e E exp_err ->
    step e exp_err
  | step_contract : forall e E ae e',
    lc e ->
    decompose e E ae ->
    contract ae e' ->
    step e (plug e' E).

End Definitions.

Hint Constructors decompose E val exp pot_redex exp val pot_redex lc' contract
                  step decompose1.
Hint Unfold open lc.

Lemma decompose_pot_redex : forall e E ae,
  decompose e E ae -> pot_redex ae.
Proof with auto. intros. induction H... Qed.

Lemma plug_ok : forall e E e',
  decompose e E e' -> plug e' E = e.
Proof.
intros.
induction H; simpl; try (auto || rewrite -> IHdecompose; auto).
Qed.

Ltac destruct_decomp e := match goal with
  |  [ H : exists E : E, exists ae : exp, decompose e E ae |- _ ] =>
       destruct H as [E [ae H]]
  | _ => fail
end.

Lemma decompose_lc : forall E e ae,
  lc e ->
  decompose e E ae ->
  lc ae.
Proof. intros. induction H0; inversion H; eauto. Qed.

Lemma decompose1_lc : forall E e ae,
  lc e ->
  decompose1 e E ae ->
  lc ae.
Proof. intros. induction H0; try (inversion H; eauto). Qed.

Ltac solve_decomp' := match goal with
  | [ H1 : lc' 0 ?e,
      IHe : val ?e \/ 
            (exists E' : E, exists ae : exp, decompose ?e E' ae)
      |- val ?exp \/ (exists E0 : E, exists ae : exp, decompose ?exp E0 ae) ]
    => (destruct IHe; right; eauto; destruct_decomp e; eauto)
  | [ |- _] => fail "solve_decomp'"
end.

Lemma ZZ : 0 = 0. reflexivity. Qed.

Ltac solve_decomp := match goal with
  | [ IH : 0 = 0 -> _ |- _ ]
    => (let Hidiot := fresh "x" in remember (IH ZZ) as Hidiot; solve_decomp')
  | [ |- _ ] => fail "flasd"
end.

Lemma decomp : forall e,
  lc e -> val e \/ 
          (exists E, exists ae, decompose e E ae).
Proof with eauto.
intros.
unfold lc in H.
remember 0.
induction H; intros; subst; try solve_decomp...
inversion H.
destruct IHlc'1. auto. right...  destruct IHlc'2. auto. eauto.
destruct_decomp e2. exists (E_app_2 H1 E)...
destruct_decomp e1. right. exists (E_app_1 E e2)...
Qed.

Hint Resolve decompose_lc decompose1_lc.

Lemma progress : forall e,
  lc e ->
  val e \/ (exists e', step e e').
Proof with eauto.
intros.
remember H as HLC.
clear HeqHLC.
apply decomp in H.
destruct H...
destruct_decomp e...
right.
assert (pot_redex ae). apply decompose_pot_redex in H...
inversion H0; subst; 
  first [ inversion H1; subst; first [destruct b; eauto | eauto]
    | eauto ].
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
  decompose e E ae ->
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
  pot_redex e -> lc e.
Proof. intros. unfold lc. inversion H; auto using lc_val. Qed.

Hint Resolve lc_active.

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
induction e; intros.
simpl...
simpl. 
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
(* abs *) 
simpl.
apply lc_abs.
inversion H; subst.
apply (IHe (S k) H3).
(* app *)
simpl; inversion H; subst;  eauto.
simpl; inversion H; subst;  eauto.
simpl; inversion H; subst;  eauto.
simpl; inversion H; subst;  eauto.
Qed.

Lemma lc_contract : forall ae e,
  lc ae ->
  contract ae e ->
  lc e.
Proof with auto.
intros.
destruct H0...
(* app *)
unfold lc in *.
inversion H; subst.
unfold open.
inversion H4; subst.
apply lc_open. exact H3. exact H5.
(* break *)
apply lc_val...
(* break *)
apply decompose1_lc with (E := E0) (e := e)...
inversion H; inversion H2; subst...
inversion H...
Qed.

Lemma preservation : forall e1 e2,
  lc e1 ->
  step e1 e2 ->
  lc e2.
Proof with auto.
intros.
unfold lc in *.
destruct H0. auto.
assert (pot_redex ae). apply decompose_pot_redex with (e := e) (E := E0)...
apply lc_active in H3.
apply lc_contract in H2...
apply lc_plug with (ae := ae) (e := e)...
Qed.


End LC.