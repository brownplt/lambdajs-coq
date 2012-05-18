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
Require Import Coq.Structures.OrderedType.
Require Import Coq.MSets.MSetList.
Require Import Coq.FSets.FMapList.
Require Import Omega.
Require Import SfLib.
Set Implicit Arguments.

Module Type ATOM.

  Parameter atom : Set.
  Declare Module Atom_as_OT : UsualOrderedType with Definition t := atom.
  Declare Module Ordered : Coq.Structures.OrderedType.OrderedType 
    with Definition t := atom.
  Parameter atom_fresh_for_list : forall (xs : list atom), 
    exists x : atom, ~ List.In x xs.

End ATOM.

Module LC (Import Atom : ATOM).

Module Atoms := Coq.MSets.MSetList.Make (Atom.Atom_as_OT).
Module AtomEnv := Coq.FSets.FMapList.Make (Atom.Ordered).

Definition atom := Atom.atom. (* free variables *)
Definition loc := Atom.atom.

Section Definitions.

Inductive exp : Set :=
  | exp_fvar : atom -> exp
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
  | exp_break : atom -> exp -> exp
  | exp_loc   : loc -> exp
  | exp_deref : exp -> exp
  | exp_ref   : exp -> exp
  | exp_set   : exp -> exp -> exp.

(* open_rec is the analogue of substitution for de Brujin indices.
  open_rec k u e replaces index k with u in e. *)
Fixpoint open_rec (k : nat) (u : exp) (e : exp) { struct e } := match e with
  | exp_fvar a    => e
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
  | exp_loc _     => e
  | exp_deref e   => exp_deref (open_rec k u e)
  | exp_ref e     => exp_ref (open_rec k u e)
  | exp_set e1 e2 => exp_set (open_rec k u e1) (open_rec k u e2)
end.

Definition open e u := open_rec 0 u e.

(* locally closed : all de Brujin indices are bound *)
Inductive lc' : nat -> exp -> Prop :=
  | lc_fvar : forall n a, lc' n (exp_fvar a)
  | lc_bvar : forall k n, k < n -> lc' n (exp_bvar k)
  | lc_abs  : forall n e,
      lc' (S n) e -> lc' n (exp_abs e)
  | lc_app  : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_app e1 e2)
  | lc_nat  : forall n x, lc' n (exp_nat x)
  | lc_succ : forall n e, lc' n e -> lc' n (exp_succ e)
  | lc_bool : forall n b, lc' n (exp_bool b)
  | lc_not  : forall n e, lc' n e -> lc' n (exp_not e)
  | lc_if   : forall n e e1 e2, 
      lc' n e -> lc' n e1 -> lc' n e2 -> lc' n (exp_if e e1 e2)
  | lc_err   : forall n, lc' n exp_err
  | lc_label : forall n x e, lc' n e -> lc' n (exp_label x e)
  | lc_break : forall n x e, lc' n e -> lc' n (exp_break x e)
  | lc_loc   : forall n x, lc' n (exp_loc x)
  | lc_ref   : forall n e, lc' n e -> lc' n (exp_ref e)
  | lc_deref : forall n e, lc' n e -> lc' n (exp_deref e)
  | lc_set   : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_set e1 e2).

Definition lc e := lc' 0 e.

Inductive val : exp -> Prop :=
  | val_abs : forall e, lc (exp_abs e) -> val (exp_abs e)
  | val_nat : forall n, val (exp_nat n)
  | val_fvar : forall a, val (exp_fvar a)
  | val_bool : forall b, val (exp_bool b)
  | val_loc  : forall l, val (exp_loc l).

Inductive tag : Set :=
  | TagAbs : tag
  | TagNat : tag
  | TagVar : tag
  | TagBool : tag
  | TagLoc : tag.

Inductive tagof : exp -> tag -> Prop :=
  | tag_abs  : forall e, tagof (exp_abs e) TagAbs
  | tag_nat  : forall n, tagof (exp_nat n) TagNat
  | tag_var  : forall x, tagof (exp_fvar x) TagVar
  | tag_bool : forall b, tagof (exp_bool b) TagBool
  | tag_loc  : forall l, tagof (exp_loc l) TagLoc.

Require Import Coq.Logic.Decidable.

Hint Constructors tagof tag.
Lemma decide_tagof : forall e t, { tagof e t } + { ~ tagof e t }.
Proof.
  intros.
  unfold not.
  destruct e; destruct t; try solve  [ auto | right; intros; inversion H ].
Qed.

Inductive E : Set :=
  | E_hole  : E
  | E_app_1 : E -> exp -> E
  | E_app_2 : forall (v : exp), val v -> E -> E
  | E_succ  : E -> E
  | E_not   : E -> E
  | E_if    : E -> exp -> exp -> E
  | E_label : atom -> E -> E
  | E_break : atom -> E -> E
  | E_ref   : E -> E
  | E_deref : E -> E
  | E_setref1 : E -> exp -> E
  | E_setref2 : forall (v : exp), val v -> E -> E.

Inductive pot_redex : exp -> Prop :=
  | redex_app  : forall e1 e2, val e1 -> val e2 -> pot_redex (exp_app e1 e2)
  | redex_succ : forall e, val e -> pot_redex (exp_succ e)
  | redex_not  : forall e, val e -> pot_redex (exp_not e)
  | redex_if   : forall e e1 e2, 
      val e -> lc e1 -> lc e2 -> pot_redex (exp_if e e1 e2)
  | redex_err  : pot_redex exp_err
  | redex_label : forall x v, val v -> pot_redex (exp_label x v)
  | redex_break : forall x v, val v -> pot_redex (exp_break x v)
  | redex_ref   : forall v, val v -> pot_redex (exp_ref v)
  | redex_deref : forall v, val v -> pot_redex (exp_deref v)
  | redex_set  : forall v1 v2, val v1 -> val v2 -> pot_redex (exp_set v1 v2).

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
      decompose (exp_label x e) (E_label x E) ae
  | cxt_ref : forall e E ae,
     decompose e E ae ->
     decompose (exp_ref e) (E_ref E) ae
  | cxt_deref : forall e E ae,
     decompose e E ae ->
     decompose (exp_deref e) (E_deref E) ae
  | cxt_set1 : forall e1 e2 E ae,
      decompose e1 E ae ->
      decompose (exp_set e1 e2) (E_setref1 E e2) ae
  | cxt_set2 : forall e1 e2 E ae (v1 : val e1),
      decompose e2 E ae ->
      decompose (exp_set e1 e2) (E_setref2 v1 E) ae.

Inductive decompose1 : exp -> E -> exp -> Prop :=
  | cxt1_hole : forall e,
      decompose1 e E_hole e
  | cxt1_app_1 : forall e1 e2,
      decompose1 (exp_app e1 e2) (E_app_1 E_hole e2) e1
  | cxt1_app_2 : forall v e (p : val v),
      decompose1 (exp_app v e) (E_app_2 p E_hole) e
  | cxt1_succ : forall e,
      decompose1 (exp_succ e) (E_succ E_hole) e
  | cxt1_not : forall e,
      decompose1 (exp_not e) (E_not E_hole) e
  | cxt1_if : forall e e1 e2,
      decompose1 (exp_if e e1 e2) (E_if E_hole e1 e2) e
  | cxt1_break : forall x e,
      decompose1 (exp_break x e) (E_break x E_hole) e
  | cxt1_ref : forall e,
     decompose1 (exp_ref e) (E_ref E_hole) e
  | cxt1_deref : forall e,
     decompose1 (exp_deref e) (E_deref E_hole) e
  | cxt1_set1 : forall e1 e2,
      decompose1 (exp_set e1 e2) (E_setref1 E_hole e2) e1
  | cxt1_set2 : forall e1 e2 (v1 : val e1),
      decompose1 (exp_set e1 e2) (E_setref2 v1 E_hole) e2.

Fixpoint plug (e : exp) (cxt : E) := match cxt with
  | E_hole => e
  | E_app_1 cxt e2 => exp_app (plug e cxt) e2
  | E_app_2 v pf cxt => exp_app v (plug e cxt)
  | E_succ cxt => exp_succ (plug e cxt)
  | E_not cxt => exp_not (plug e cxt)
  | E_if cxt e1 e2 => exp_if (plug e cxt) e1 e2
  | E_label x cxt => exp_label x (plug e cxt)
  | E_break x cxt => exp_break x (plug e cxt)
  | E_ref cxt => exp_ref (plug e cxt)
  | E_deref cxt => exp_deref (plug e cxt)
  | E_setref1 cxt e2 => exp_set (plug e cxt) e2
  | E_setref2 v1 _ cxt => exp_set v1 (plug e cxt)
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
  | contract_app_err : forall v1 v2,
      val v1 ->
      val v2 ->
      ~ tagof v1 TagAbs ->
      contract (exp_app v1 v2) exp_err
  | contract_if_err : forall v1 e2 e3,
      val v1 ->
      ~ tagof v1 TagBool ->
      contract (exp_if v1 e2 e3) exp_err
  | contract_label : forall x v,
      val v -> contract (exp_label x v) v
  | contract_break_bubble : forall x v E e,
    decompose1 e E (exp_break x v) ->
    contract e (exp_break x v)
  | contract_break_match : forall x v,
    contract (exp_label x (exp_break x v)) v
  | contract_break_mismatch : forall x y v,
    x <> y ->
    contract (exp_label x (exp_break y v)) (exp_break y v)
  | contract_set_err : forall v1 v2,
      val v1 ->
      val v2 ->
      ~ tagof v1 TagLoc ->
      contract (exp_set v1 v2) exp_err
  | contract_deref_err : forall v,
      val v ->
      ~ tagof v TagLoc ->
      contract (exp_deref v) exp_err
  | contract_err_bubble : forall e E,
      decompose e E exp_err ->
      contract e exp_err.

Inductive stored_val : Set :=
  | val_with_proof : forall (v : exp), val v -> stored_val.

Definition sto := AtomEnv.t stored_val.

Inductive step : sto -> exp -> sto -> exp -> Prop :=
  (* Slightly strange: exp_err -> exp_err -> exp_err -> ... *)
  | step_err : forall s e E,
    lc e ->
    decompose e E exp_err ->
    step s e s exp_err
  | step_contract : forall s e E ae e',
    lc e ->
    decompose e E ae ->
    contract ae e' ->
    step s e s (plug e' E)
  | step_ref : forall E e v l s (pf : val v),
    lc e ->
    decompose e E (exp_ref v) ->
    ~ In l (map (@fst AtomEnv.key stored_val) (AtomEnv.elements s)) ->
    step s e (AtomEnv.add l (val_with_proof pf) s) (plug (exp_loc l) E)
  | step_deref : forall e s E l v (pf : val v),
    lc e ->
    decompose e E (exp_deref (exp_loc l)) ->
    AtomEnv.find l s = Some (val_with_proof pf) ->
    step s e s (plug v E)
  | step_deref_err : forall e s E l,
    lc e ->
    decompose e E (exp_deref (exp_loc l)) ->
    AtomEnv.find l s = None ->
    step s e s (plug exp_err E)
  | step_setref : forall s e E l v v_old (pf_v : val v) (pf_v_old : val v_old),
    lc e ->
    decompose e E (exp_set (exp_loc l) v) ->
    AtomEnv.find l s = Some (val_with_proof pf_v_old) ->
    step s e (AtomEnv.add l (val_with_proof pf_v) s) (plug (exp_loc l) E)
  | step_setref_err : forall s e E l v,
    lc e ->
    decompose e E (exp_set (exp_loc l) v) ->
    AtomEnv.find l s = None ->
    step s e s (plug exp_err E).

End Definitions.

Tactic Notation "exp_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "exp_fvar"
    | Case_aux c "exp_bvar"
    | Case_aux c "exp_abs"
    | Case_aux c "exp_app"
    | Case_aux c "exp_nat"
    | Case_aux c "exp_succ"
    | Case_aux c "exp_bool"
    | Case_aux c "exp_not"
    | Case_aux c "exp_if"
    | Case_aux c "exp_err"
    | Case_aux c "exp_label"
    | Case_aux c "exp_break"
    | Case_aux c "exp_loc"
    | Case_aux c "exp_ref"
    | Case_aux c "exp_deref"
    | Case_aux c "exp_set" ].
Tactic Notation "lc_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "lc_fvar"
    | Case_aux c "lc_bvar"
    | Case_aux c "lc_abs"
    | Case_aux c "lc_app"
    | Case_aux c "lc_nat"
    | Case_aux c "lc_succ"
    | Case_aux c "lc_bool"
    | Case_aux c "lc_not"
    | Case_aux c "lc_if"
    | Case_aux c "lc_err"
    | Case_aux c "lc_label"
    | Case_aux c "lc_break"
    | Case_aux c "lc_loc"
    | Case_aux c "lc_ref"
    | Case_aux c "lc_deref"
    | Case_aux c "lc_set" ].
Tactic Notation "val_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "val_abs"
    | Case_aux c "val_nat"
    | Case_aux c "val_fvar"
    | Case_aux c "val_bool"
    | Case_aux c "val_loc" ].
Tactic Notation "E_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "E_hole"
    | Case_aux c "E_app_1"
    | Case_aux c "E_app_2"
    | Case_aux c "E_succ"
    | Case_aux c "E_not"
    | Case_aux c "E_if"
    | Case_aux c "E_label"
    | Case_aux c "E_break"
    | Case_aux c "E_ref"
    | Case_aux c "E_deref"
    | Case_aux c "E_setref1"
    | Case_aux c "E_setref2" ].
Tactic Notation "redex_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "redex_app"
    | Case_aux c "redex_succ"
    | Case_aux c "redex_not"
    | Case_aux c "redex_if"
    | Case_aux c "redex_err"
    | Case_aux c "redex_label"
    | Case_aux c "redex_break"
    | Case_aux c "redex_ref"
    | Case_aux c "redex_deref"
    | Case_aux c "redex_set" ].
Tactic Notation "decompose_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "decompose_hole"
    | Case_aux c "decompose_app_1"
    | Case_aux c "decompose_app_2"
    | Case_aux c "decompose_succ"
    | Case_aux c "decompose_not"
    | Case_aux c "decompose_if"
    | Case_aux c "decompose_break"
    | Case_aux c "decompose_label"
    | Case_aux c "decompose_ref"
    | Case_aux c "decompose_deref"
    | Case_aux c "decompose_set1"
    | Case_aux c "decompose_set2" ].
Tactic Notation "decompose1_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "decompose1_hole"
    | Case_aux c "decompose1_app_1"
    | Case_aux c "decompose1_app_2"
    | Case_aux c "decompose1_succ"
    | Case_aux c "decompose1_not"
    | Case_aux c "decompose1_if"
    | Case_aux c "decompose1_break"
    | Case_aux c "decompose1_ref"
    | Case_aux c "decompose1_deref"
    | Case_aux c "decompose1_set1"
    | Case_aux c "decompose1_set2" ].
Tactic Notation "contract_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "contract_succ"
    | Case_aux c "contract_not"
    | Case_aux c "contract_if1"
    | Case_aux c "contract_if2"
    | Case_aux c "contract_app"
    | Case_aux c "contract_app_err"
    | Case_aux c "contract_if_err"
    | Case_aux c "contract_label"
    | Case_aux c "contract_break_bubble"
    | Case_aux c "contract_break_match"
    | Case_aux c "contract_break_mismatch"
    | Case_aux c "contract_set_err"
    | Case_aux c "contract_deref_err"
    | Case_aux c "contract_err_bubble" ].
Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "step_err"
  | Case_aux c "step_contract"
  | Case_aux c "step_ref"
  | Case_aux c "step_deref"
  | Case_aux c "step_deref_err"
  | Case_aux c "step_setref"
  | Case_aux c "step_setref_err" ].

Hint Constructors decompose E val exp pot_redex exp val pot_redex lc' contract
                  step decompose1 stored_val.
Hint Unfold open lc.

Lemma decompose_pot_redex : forall e E ae,
  decompose e E ae -> pot_redex ae.
Proof with auto. intros. induction H... Qed.

Lemma plug_ok : forall e E e',
  decompose e E e' -> plug e' E = e.
Proof.
intros.
decompose_cases (induction H) Case; simpl; try (auto || rewrite -> IHdecompose; auto).
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
Proof. intros. decompose_cases (induction H0) Case; inversion H; eauto. Qed.

Lemma decompose1_lc : forall E e ae,
  lc e ->
  decompose1 e E ae ->
  lc ae.
Proof. intros. decompose1_cases (induction H0) Case; inversion H; eauto. Qed.

Ltac solve_decomp' := match goal with
  | [ H1 : lc' 0 ?e,
      IHe : val ?e \/ 
            (exists E' : E, exists ae : exp, decompose ?e E' ae)
      |- val ?exp \/ (exists E0 : E, exists ae : exp, decompose ?exp E0 ae) ]
    => (destruct IHe; right; eauto; destruct_decomp e; eauto)
  | [ |- _] => fail "solve_decomp'"
end.

Ltac solve_decomp := match goal with
  | [ IH : 0 = 0 -> _ |- _ ]
    => (remember (IH (eq_refl 0)); solve_decomp')
  | [ |- _ ] => fail "flasd"
end.

Lemma decomp : forall e,
  lc e -> val e \/ 
          (exists E, exists ae, decompose e E ae).
Proof with eauto.
intros.
unfold lc in H.
remember 0.
lc_cases (induction H) Case; intros; subst; try solve_decomp...
Case "lc_bvar". inversion H.
Case "lc_app".
  destruct IHlc'1. auto. right...  destruct IHlc'2. auto. eauto.
  destruct_decomp e2. exists (E_app_2 H1 E)...
  destruct_decomp e1. right. exists (E_app_1 E e2)...
Case "lc_set".
  destruct IHlc'1. auto. right...  destruct IHlc'2. auto. eauto.
  destruct_decomp e2. exists (E_setref2 H1 E)...
  destruct_decomp e1. right. exists (E_setref1 E e2)...
Qed.

Hint Resolve decompose_lc decompose1_lc.
Hint Unfold not.

(* Invert tagof *)
Hint Extern 1 ( False ) => match goal with
  | [ H: tagof _ _ |- False]  => inversion H
end.

Lemma progress : forall sto e,
  lc e ->
  val e \/ (exists e', exists sto', step sto e sto' e').
Proof with eauto.
intros.
remember H as HLC; clear HeqHLC.
apply decomp in H.
destruct H...
destruct_decomp e...
right.
assert (pot_redex ae). apply decompose_pot_redex in H...


redex_cases (inversion H0) Case; subst...
Case "redex_app". val_cases (inversion H1) SCase; subst; eauto 6.
Case "redex_if". val_cases (inversion H1) SCase; subst; first [destruct b; eauto 6 | eauto 6]. 
Case "redex_ref".
assert (exists l : atom, 
          ~ In l (map (@fst AtomEnv.key stored_val) (AtomEnv.elements sto0))) 
    as [l HnotInL].
  apply Atom.atom_fresh_for_list.
exists (plug (exp_loc l) E).
exists (AtomEnv.add l (val_with_proof H1) sto0)...
Case "redex_deref".
val_cases (inversion H1) SCase; subst; try solve [ exists (plug exp_err E); eauto ].
  SCase "val_loc". remember (AtomEnv.find l sto0) as MaybeV.
  destruct MaybeV...
  destruct s...
Case "redex_set".
val_cases (inversion H1) SCase; subst; try solve [ exists (plug exp_err E); eauto ].
  SCase "val_loc". remember (AtomEnv.find l sto0) as MaybeV.
  destruct MaybeV...
  destruct s.
  exists (plug (exp_loc l) E).
  exists (AtomEnv.add l (val_with_proof H2) sto0)...
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
decompose_cases (induction H1) Case; first [ inversion H; subst; simpl; unfold lc in *; solve_lc_plug | auto ].
Qed.

Hint Resolve lc_plug.

Lemma lc_val : forall v,
  val v -> lc' 0 v.
Proof with auto.
intros. inversion H... Qed.

Lemma lc_active : forall e,
  pot_redex e -> lc e.
Proof. intros. unfold lc. inversion H; auto using lc_val. Qed.

Hint Resolve lc_active lc_val.

Lemma lc_ascend : forall k k' e, k' >= k -> lc' k e -> lc' k' e.
Proof with auto.
intros.
generalize dependent k'.
lc_cases (induction H0) Case...
Case "lc_bvar".
  intros. apply lc_bvar. omega.
Case "lc_abs".
  intros. apply lc_abs. apply IHlc'. omega.
Qed.

Lemma lc_open : forall k e u,
  lc' (S k) e ->
  lc' 0 u ->
  lc' k (open_rec k u e).
Proof with auto.
intros.
generalize dependent k.
exp_cases (induction e) Case; intros; try solve [simpl; inversion H; subst;  eauto].
Case "exp_bvar".
  simpl. 
  assert (k >= n \/ k < n). apply le_or_lt.
  destruct H1.
  SCase "k >= n".
    assert ({ k = n } + { k <> n }). decide equality.
    destruct H2.
    SSCase "k = n".
    assert (beq_nat k n = true). rewrite -> beq_nat_true_iff...
    rewrite -> H2.  assert (k >= 0). omega.
    apply lc_ascend with (k := 0) (k' := k)...
    SSCase "k <> n".
    assert (beq_nat k n = false).  rewrite -> beq_nat_false_iff...
    rewrite -> H2.
    assert (n < k). omega. auto...
  SCase "k < n".
    assert (beq_nat k n = false).  rewrite -> beq_nat_false_iff... omega.
    rewrite -> H2. apply lc_bvar.
    clear H2.
    inversion H; subst.
    assert False. omega.
    inversion H2.
Qed.

Lemma lc_contract : forall ae e,
  lc ae ->
  contract ae e ->
  lc e.
Proof with auto.
intros.
contract_cases (destruct H0) Case...
Case "contract_succ". simpl. exp_cases (destruct e) SCase; auto.
Case "contract_not". simpl. exp_cases (destruct e) SCase; auto.
Case "contract_if1". inversion H...
Case "contract_if2". inversion H...
Case "contract_app".
  unfold lc in *.
  inversion H; subst.
  unfold open.
  inversion H4; subst.
  apply lc_open. exact H3. exact H5.
Case "contract_break_bubble".
  apply decompose1_lc with (E := E0) (e := e)...
Case "contract_break_match".
  inversion H; inversion H2; subst...
Case "contract_break_mismatch".
  inversion H...
Qed.

Lemma preservation : forall sto1 e1 sto2 e2,
  lc e1 ->
  step sto1 e1 sto2 e2 ->
  lc e2.
Proof with auto.
intros.
unfold lc in *.
step_cases (destruct H0) Case. 
Case "step_err"; auto.
Case "step_contract".
  apply lc_contract in H2... apply lc_plug with (ae := ae) (e := e)...
  apply lc_active. apply decompose_pot_redex with (e := e) (E := E0)...
Case "step_ref".
  apply lc_plug with (e := e) (ae := exp_ref v)...
Case "step_deref".
  apply lc_plug with (e := e) (ae := exp_deref (exp_loc l))...
Case "step_deref_err".
  apply lc_plug with (e := e) (ae := exp_deref (exp_loc l))...
Case "step_setref".
  apply lc_plug with (e := e) (ae := exp_set (exp_loc l) v)...
Case "step_setref_err".
  apply lc_plug with (e := e) (ae := exp_set (exp_loc l) v)...
Qed.

End LC.
