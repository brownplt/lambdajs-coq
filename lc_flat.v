(* 
 * An encoding of the untyped lambda calculus with numbers.
 *
 * Authors: Arjun Guha <arjun@cs.brown.edu>
 *)
Require Import Coq.Arith.EqNat.
Set Implicit Arguments.

Parameter atom : Set. (* free variables *)

Axiom atom_eqdec : forall (x y : atom), { x = y } + { x <> y }.

Section Definitions.

Inductive exp : Set :=
  | exp_var  : atom -> exp
  | exp_bvar : nat -> exp (* bound variables as de Brujin indices *)
  | exp_abs  : exp -> exp
  | exp_app  : exp -> exp -> exp
  | exp_nat  : nat -> exp
  | exp_succ : exp -> exp
  | exp_bool : bool -> exp
  | exp_not  : exp -> exp
  | exp_if   : exp -> exp -> exp -> exp
  | exp_err  : exp
  | exp_label : atom -> exp -> exp
  | exp_break : atom -> exp -> exp.

(* open_rec is the analogue of substitution for de Brujin indices.
  open_rec k u e replaces index k with u in e. *)
Fixpoint open_rec (k : nat) (u : exp) (e : exp) { struct e } := match e with
  | exp_var _     => e
  | exp_bvar n    => if beq_nat k n then u else e
  | exp_abs  e    => exp_abs (open_rec (S k) u e)
  | exp_app e1 e2 => exp_app (open_rec k u e1) (open_rec k u e2)
  | exp_nat n     => e
  | exp_succ e    => exp_succ (open_rec k u e)
  | exp_bool b     => e
  | exp_not e      => exp_not (open_rec k u e)
  | exp_if e e1 e2 => exp_if (open_rec k u e) (open_rec k u e1) (open_rec k u e2)
  | exp_err       => e
  | exp_label x e => exp_label x (open_rec k u e)
  | exp_break x e => exp_break x (open_rec k u e)
end.

Definition open e u := open_rec 0 u e.

(* locally closed : all de Brujin indices are bound *)
Inductive lc : exp -> Prop :=
  | lc_var  : forall x, lc (exp_var x)
  | lc_abs  : forall x e, lc (open e x) -> lc (exp_abs e)
  | lc_app  : forall e1 e2, lc e1 -> lc e2 -> lc (exp_app e1 e2)
  | lc_nat  : forall n, lc (exp_nat n)
  | lc_succ : forall e, lc e -> lc (exp_succ e)
  | lc_bool : forall b, lc (exp_bool b)
  | lc_not  : forall e, lc e -> lc (exp_not e)
  | lc_if   : forall e e1 e2, lc e -> lc e1 -> lc e2 -> lc (exp_if e e1 e2)
  | lc_err  : lc exp_err
  | lc_label : forall x e, lc e -> lc (exp_label x e)
  | lc_break : forall x e, lc e -> lc (exp_break x e).


Inductive val : exp -> Prop :=
  | val_var : forall x, val (exp_var x)
  | val_abs : forall e, val (exp_abs e)
  | val_nat : forall n, val (exp_nat n)
  | val_bool : forall b, val (exp_bool b).

Inductive E : Set :=
  | E_hole  : E
  | E_app_1 : E -> exp -> E
  | E_app_2 : forall (v : exp), val v -> E -> E
  | E_succ  : E -> E
  | E_not   : E -> E
  | E_if    : E -> exp -> exp -> E
  | E_label : atom -> E -> E
  | E_break : atom -> E -> E.


Inductive pot_redex : exp -> Prop :=
  | redex_app  : forall e1 e2, val e1 -> val e2 -> pot_redex (exp_app e1 e2)
  | redex_succ : forall e, val e -> pot_redex (exp_succ e)
  | redex_not  : forall e, val e -> pot_redex (exp_not e)
  | redex_if   : forall e e1 e2, val e -> pot_redex (exp_if e e1 e2)
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
  | cxt_succ : forall E e e',
      decompose e E e' ->
      decompose (exp_succ e) (E_succ E) e'
  | cxt_not : forall E e e',
      decompose e E e' ->
      decompose (exp_not e) (E_not E) e'
  | cxt_if : forall E e e1 e2 e',
      decompose e E e' ->
      decompose (exp_if e e1 e2) (E_if E e1 e2) e'
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
  | cxt1_succ : forall e,
      decompose1 (exp_succ e) (E_succ E_hole) e
  | cxt1_not : forall e e',
      decompose1 (exp_not e) (E_not E_hole) e'
  | cxt1_if : forall e e1 e2 e',
      decompose1 (exp_if e e1 e2) (E_if E_hole e1 e2) e'
  | cxt1_break : forall x e,
      decompose1 (exp_break x e) (E_break x E_hole) e.

Fixpoint plug (e : exp) (cxt : E) := match cxt with
  | E_hole => e
  | E_app_1 cxt e2 => exp_app (plug e cxt) e2
  | E_app_2 v pf cxt => exp_app v (plug e cxt)
  | E_succ cxt => exp_succ (plug e cxt)
  | E_not cxt => exp_not (plug e cxt)
  | E_if cxt e1 e2 => exp_if (plug e cxt) e1 e2
  | E_label x cxt => exp_label x (plug e cxt)
  | E_break x cxt => exp_break x (plug e cxt)
end.

Fixpoint delta exp := match exp with
  | exp_succ (exp_nat n) => exp_nat (S n)
  | exp_not (exp_bool b) => exp_bool (negb b)
  | _                    => exp_err
end.

Inductive contract :  exp -> exp -> Prop := 
  | contract_succ : forall e, contract (exp_succ e) (delta (exp_succ e))
  | contract_not  : forall e, contract (exp_not e) (delta (exp_not e))
  | contract_if1  : forall e1 e2, contract (exp_if (exp_bool true) e1 e2) e1
  | contract_if2  : forall e1 e2, contract (exp_if (exp_bool false) e1 e2) e2
  | contract_app  : forall e v, 
      val v -> contract (exp_app (exp_abs e) v) (open e v)
  | contract_err_app1 : forall n v,
      val v -> contract (exp_app (exp_nat n) v) exp_err
  | contract_err_app2 : forall x v,
      val v -> contract (exp_app (exp_var x) v) exp_err
  | contract_err_app3 : forall b v,
      val v -> contract (exp_app (exp_bool b) v) exp_err
  | contract_err_if1 : forall e e1 e2,
      contract (exp_if (exp_abs e) e1 e2) exp_err
  | contract_err_if2 : forall x e1 e2,
      contract (exp_if (exp_var x) e1 e2) exp_err
  | contract_err_if3 : forall n e1 e2,
      contract (exp_if (exp_nat n) e1 e2) exp_err
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

Hint Constructors decompose E val exp pot_redex exp val pot_redex lc contract
                  step decompose1.
Hint Unfold open.

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

Ltac solve_decomp := match goal with
  | [ H1 : lc ?e,
      IHe : val ?e \/ 
            (exists E' : E, exists ae : exp, decompose ?e E' ae)
      |- val ?exp \/ (exists E0 : E, exists ae : exp, decompose ?exp E0 ae) ]
    => (destruct IHe; right; eauto; destruct_decomp e; eauto)
  | _ => fail
end.

Lemma decomp : forall e,
  lc e -> val e \/ 
          (* (exists e', exists x, e = exp_label x e') \/  *)
          (exists E, exists ae, decompose e E ae).
Proof with eauto.
intros.
induction H; intros; try solve_decomp...
(* exp_app *)
destruct IHlc1; right...  destruct IHlc2...
destruct_decomp e2. exists (E_app_2 H1 E)...
destruct_decomp e1. exists (E_app_1 E e2)...
Qed.

Hint Resolve decompose_lc.

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
  | [ IHdecompose : lc ?e -> lc (plug ?e' ?E),
      H : lc ?e
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
induction H1; first [ inversion H; subst; simpl; solve_lc_plug | auto ].
Qed.

Hint Resolve lc_plug.
