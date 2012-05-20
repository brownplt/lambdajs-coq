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
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.
Require Import Omega.
Require Import SfLib.
Set Implicit Arguments.

Module Type ATOM.

  Parameter atom : Set.
  Declare Module Atom_as_OT : UsualOrderedType with Definition t := atom.
  Declare Module Ordered : Coq.Structures.OrderedType.OrderedType 
    with Definition t := atom.
  Module OrderedTypeFacts := Coq.Structures.OrderedType.OrderedTypeFacts (Ordered).
  Parameter atom_fresh_for_list : forall (xs : list atom), 
    exists x : atom, ~ List.In x xs.
  Parameter atom_eq_dec : forall a1 a2 : atom, {a1 = a2} + {~ a1 = a2}.
  Parameter atom_dec_eq : forall a1 a2 : atom, a1 = a2 \/ ~ a1 = a2.

End ATOM.

Module Type STRING.

 Parameter string : Set.
 Declare Module String_as_OT : UsualOrderedType with Definition t := string.
 Declare Module Ordered : Coq.Structures.OrderedType.OrderedType
   with Definition t := string.
 Module OrderedTypeFacts := Coq.Structures.OrderedType.OrderedTypeFacts (Ordered).
 Parameter string_eq_dec : forall s1 s2 : string, {s1 = s2} + {~ s1 = s2}.
 Parameter string_dec_eq : forall s1 s2 : string, s1 = s2 \/ ~ s1 = s2.

End STRING.

Module LC (Import Atom : ATOM) (Import String : STRING).

Module Atoms := Coq.MSets.MSetList.Make (Atom.Atom_as_OT).
Module AtomEnv := Coq.FSets.FMapList.Make (Atom.Ordered).

Definition atom := Atom.atom. (* free variables *)
Definition loc := Atom.atom.
Definition string := String.string.


Section ListLemmas.

Lemma in_dec_dec_list :
  (forall A (l1 : list A) l2, (forall a1 a2, In a1 l1 -> In a2 l2 -> a1 = a2 \/ a1 <> a2) -> (l1 = l2 \/ l1 <> l2)).
Proof with eauto.
induction l1. intros. destruct l2; [left; auto | right; congruence].
induction l2. intros. right; congruence. intros. assert (a = a0 \/ a <> a0). apply H; constructor...
assert (l1 = l2 \/ l1 <> l2). apply IHl1. intros. apply H. right... right...
inversion H0; subst.  inversion H1; subst. left; auto. right; congruence. right; congruence.
Qed.

Lemma forall_dec_dec_exists : forall A (P : A -> Prop) (l : list A), (forall a1 a2 : A, a1 = a2 \/ ~ a1 = a2) 
  -> Forall (fun e => P e \/ ~ P e) l
  -> decidable (exists e, In e l /\ P e).
Proof with eauto.
intros. unfold decidable in *. induction H0. right; intro. inversion H0. inversion H1. inversion H2.
inversion H0. left. exists x. split... constructor...
inversion IHForall. inversion H3. left; exists x0. inversion H4; split... assert (D := H x x0). 
destruct D. subst. contradiction. right. auto.
right. intro. apply H3. inversion H4. exists x0. inversion H5; split... assert (D := H x x0). 
destruct D. subst. contradiction. inversion H6. contradiction. auto.
Qed.

Lemma forall_dec_dec_forall : forall A (P : A -> Prop) (l : list A), 
  Forall (fun e => P e \/ ~ P e) l -> (Forall P l) \/ ~ (Forall P l).
Proof with eauto.
induction l. intros. left; constructor.
intros. inversion H.
assert (Forall P l \/ ~ Forall P l). apply IHl. apply H3. 
inversion H2. inversion H4. left; constructor... right; intro. apply H6. inversion H7...
right. intro. apply H5. inversion H6...
Qed.

Lemma split_components : forall A B (l : list (A*B)), (split l = (fst (split l), snd (split l))).
induction l. reflexivity. remember a as a'; destruct a'; simpl. rewrite IHl. reflexivity.
Qed.

Lemma map_snd_snd_split : forall A B (l : list (A*B)), map (@snd A B) l = snd (split l).
Proof with eauto.
induction l. reflexivity. unfold map. fold (map (@snd A B) l). rewrite IHl. 
simpl. remember a as a'; destruct a'. simpl. 
rewrite split_components. reflexivity.
Qed.
Lemma map_fst_fst_split : forall A B (l : list (A*B)), map (@fst A B) l =  fst (split l).
Proof with eauto.
induction l. reflexivity. unfold map. fold (map (@fst A B) l). rewrite IHl. 
simpl. remember a as a'; destruct a'. simpl. 
rewrite split_components. reflexivity.
Qed.

Lemma take_while A (l : list A)
  (P : A -> Prop) (dec : forall x, In x l -> decidable (P x)) : 
  (Forall P l) \/ (exists (l1 l2 : list A) (x : A), l = l1 ++ x :: l2 /\ Forall P l1 /\ ~ P x).
Proof with eauto.
  induction l. left; constructor...
  assert (D := forall_dec_dec_forall P (l:=l)).
  assert (Forall P l \/ ~ Forall P l). apply D. unfold decidable in dec. rewrite Forall_forall. intros. apply dec.
  right...
  assert (P a \/ ~ P a). apply dec. left...
  inversion H. inversion H0. left. constructor... right. exists []; exists l; exists a. auto.
  assert (Forall P l \/ exists l1 l2 x, l = l1 ++ x :: l2 /\ Forall P l1 /\ ~ P x). apply IHl. intros. apply dec.
  right...
  inversion H2. contradiction. clear H2. 
  inversion H0. inversion H3. inversion H4. inversion H5. right. exists (a :: x). exists x0. exists x1. inversion H6. split. rewrite H7... inversion H8. split... 
  right. exists []; exists l; exists a...
Qed.

Lemma forall_fst_comm : forall A B (l : list (A*B)) (P : A -> Prop),
  Forall (fun ab : A*B => P (fst ab)) l -> Forall P (fst (split l)).
Proof with eauto.
  induction l; intros. constructor. remember a as a'; destruct a'. simpl.
  rewrite (split_components l). simpl. inversion H. constructor. auto. apply IHl. auto.
Qed.
Lemma forall_snd_comm : forall A B (l : list (A*B)) (P : B -> Prop),
  Forall (fun ab : A*B => P (snd ab)) l -> Forall P (snd (split l)).
Proof with eauto.
  induction l; intros. constructor. remember a as a'; destruct a'. simpl.
  rewrite (split_components l). simpl. inversion H. constructor. auto. apply IHl. auto.
Qed.

Lemma fst_split_comm : forall A B l1 (ab : A*B) l2, 
  fst (split (l1 ++ ab :: l2)) = fst (split l1) ++ fst ab :: fst (split l2).
Proof with eauto.
  induction l1; intros. destruct ab as (a,b).
  simpl. induction l2; intros. reflexivity.
  destruct a0 as (a0, b0). simpl. rewrite (split_components l2) in *. reflexivity.
  destruct a as (a0, b0). simpl. rewrite (split_components (l1 ++ ab :: l2)). simpl.
  rewrite (split_components l1). simpl. rewrite IHl1. reflexivity.
Qed.
Lemma snd_split_comm : forall A B l1 (ab : A*B) l2, 
  snd (split (l1 ++ ab :: l2)) = snd (split l1) ++ snd ab :: snd (split l2).
Proof with eauto.
  induction l1; intros. destruct ab as (a,b).
  simpl. induction l2; intros. reflexivity.
  destruct a0 as (a0, b0). simpl. rewrite (split_components l2) in *. reflexivity.
  destruct a as (a0, b0). simpl. rewrite (split_components (l1 ++ ab :: l2)). simpl.
  rewrite (split_components l1). simpl. rewrite IHl1. reflexivity.
Qed.

Lemma fst_split_cons : forall A B a b (l : list (A*B)), fst (split ((a, b) :: l)) = a :: fst (split l). 
  intros. simpl. rewrite (split_components l); simpl. reflexivity.
Qed.
Lemma snd_split_cons : forall A B a b (l : list (A*B)), snd (split ((a, b) :: l)) = b :: snd (split l). 
  intros. simpl. rewrite (split_components l); simpl. reflexivity.
Qed.

Lemma fst_split_map_snd : forall A B C (l : list (A*B)) (P : B -> C),
  fst (split (map (fun ab => (fst ab, P (snd ab))) l)) = fst (split l).
Proof with eauto.
  induction l; intros. reflexivity.
  destruct a as (a,b). simpl. 
  rewrite (split_components l). rewrite (split_components (map (fun ab => (fst ab, P (snd ab))) l)). simpl.
  f_equal. apply IHl.
Qed.

Lemma snd_split_map_fst : forall A B C (l : list (A*B)) (P : A -> C),
  snd (split (map (fun ab => (P (fst ab), snd ab)) l)) = snd (split l).
Proof with eauto.
  induction l; intros. reflexivity.
  destruct a as (a,b). simpl. 
  rewrite (split_components l). rewrite (split_components (map (fun ab => (P (fst ab), snd ab)) l)). simpl.
  f_equal. apply IHl.
Qed.


Lemma forall_app : forall A (l1 : list A) l2 P, Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof with eauto.
intros. split. induction l1. simpl... intro. inversion H. split. constructor... apply (IHl1 H3). apply (IHl1 H3).
intros. inversion H. induction l1. simpl... constructor. inversion H0... fold (l1 ++ l2). apply IHl1. split...
inversion H0... inversion H0...
Qed.

Lemma forall_map_comm : forall A B (l : list A) P (f : A -> B), Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof with eauto.
  intros; induction l. simpl. split; intros; constructor.
  split. intros. simpl in H. inversion H. constructor... apply IHl...
  intros. inversion H. simpl. constructor... apply IHl...
Qed.

Lemma Forall_in : forall A (l : list A) (P : A -> Prop) e, Forall P l -> In e l -> P e.
Proof with auto.
intros. induction H. inversion H0.
inversion H0. subst. auto. auto.
Qed.

Lemma in_middle : forall A (l1 : list A) e l2, In e (l1 ++ e :: l2).
intros.
induction l1. simpl; left; auto. simpl. right; auto.
Qed.

End ListLemmas.

Section Definitions.

Inductive exp : Set :=
  | exp_fvar  : atom -> exp
  | exp_bvar  : nat -> exp (* bound variables as de Brujin indices *)
  | exp_abs   : exp -> exp
  | exp_app   : exp -> exp -> exp
  | exp_nat   : nat -> exp
  | exp_succ  : exp -> exp
  | exp_bool  : bool -> exp
  | exp_not   : exp -> exp
  | exp_if    : exp -> exp -> exp -> exp
  | exp_err   : exp
  | exp_label : atom -> exp -> exp
  | exp_break : atom -> exp -> exp
  | exp_loc   : loc -> exp
  | exp_deref : exp -> exp
  | exp_ref   : exp -> exp
  | exp_set   : exp -> exp -> exp
  | exp_catch : exp -> exp -> exp (* 2nd exp is a binder *)
  | exp_throw : exp -> exp
  | exp_seq   : exp -> exp -> exp
  | exp_finally : exp -> exp -> exp
  | exp_obj   : list (string * exp) -> exp.
Reset exp_ind.
Definition exp_ind := fun (P : exp -> Prop)
  (f : forall a : atom, P (exp_fvar a))
  (f0 : forall n : nat, P (exp_bvar n))
  (f1 : forall e : exp, P e -> P (exp_abs e))
  (f2 : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_app e e0))
  (f3 : forall n : nat, P (exp_nat n))
  (f4 : forall e : exp, P e -> P (exp_succ e))
  (f5 : forall b : bool, P (exp_bool b))
  (f6 : forall e : exp, P e -> P (exp_not e))
  (f7 : forall e : exp, P e -> forall e0 : exp, P e0 -> forall e1 : exp, P e1 -> P (exp_if e e0 e1))
  (f8 : P exp_err)
  (f9 : forall (a : atom) (e : exp), P e -> P (exp_label a e))
  (f10 : forall (a : atom) (e : exp), P e -> P (exp_break a e))
  (f11 : forall l : loc, P (exp_loc l))
  (f12 : forall e : exp, P e -> P (exp_deref e))
  (f13 : forall e : exp, P e -> P (exp_ref e))
  (f14 : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_set e e0))
  (f15 : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_catch e e0))
  (f16 : forall e : exp, P e -> P (exp_throw e))
  (f17 : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_seq e e0))
  (f18 : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_finally e e0))
  (f19 : forall l : list (string * exp), Forall P (map (@snd string exp) l) -> P (exp_obj l)) =>
fix exp_rec' (e : exp) {struct e} : P e :=
  match e as e0 return (P e0) with
  | exp_fvar a => f a
  | exp_bvar n => f0 n
  | exp_abs e0 => f1 e0 (exp_rec' e0)
  | exp_app e0 e1 => f2 e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_nat n => f3 n
  | exp_succ e0 => f4 e0 (exp_rec' e0)
  | exp_bool b => f5 b
  | exp_not e0 => f6 e0 (exp_rec' e0)
  | exp_if e0 e1 e2 => f7 e0 (exp_rec' e0) e1 (exp_rec' e1) e2 (exp_rec' e2)
  | exp_err => f8
  | exp_label a e0 => f9 a e0 (exp_rec' e0)
  | exp_break a e0 => f10 a e0 (exp_rec' e0)
  | exp_loc l => f11 l
  | exp_deref e0 => f12 e0 (exp_rec' e0)
  | exp_ref e0 => f13 e0 (exp_rec' e0)
  | exp_set e0 e1 => f14 e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_catch e0 e1 => f15 e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_throw e0 => f16 e0 (exp_rec' e0)
  | exp_seq e0 e1 => f17 e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_finally e0 e1 => f18 e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_obj l =>
    f19 l ((fix forall_rec (ls : list (string * exp)) : Forall P (map (@snd string exp) ls) :=
      match ls with
        | nil => Forall_nil P
        | (_,tr)::rest => Forall_cons tr (exp_rec' tr) (forall_rec rest)
      end) l)
  end.
(* Definition exp_rec := fun (P : exp -> Set) => exp_rect (P := P). *)
(* Definition exp_ind := fun (P : exp -> Prop) => exp_rect (P := P). *)


Ltac destruct_and_solve' e := destruct e; [idtac | right; intro Neq; inversion Neq; contradiction].
Tactic Notation "solve" "by" "destruction" "1" tactic(t) constr(e) := destruct_and_solve' e; left; t; auto.
Tactic Notation "solve" "by" "destruction" "2" tactic(t) constr(e1) constr(e2) := 
  destruct_and_solve' e1; solve by destruction 1 (t) e2.
Tactic Notation "solve" "by" "destruction" "3" tactic(t) constr(e1) constr(e2) constr (e3) := 
  destruct_and_solve' e1; solve by destruction 2 (t) e2 e3.

Lemma exp_eq_dec : forall e1 e2 : exp, e1 = e2 \/ ~ e1 = e2.
Proof with eauto.
induction e1; induction e2; try solve [
  left; reflexivity | right; congruence
  | solve by destruction 1 subst (IHe1 e2)
  | solve by destruction 2 subst (IHe1_1 e2_1) (IHe1_2 e2_2)
  | solve by destruction 3 subst (IHe1_1 e2_1) (IHe1_2 e2_2) (IHe1_3 e2_3)
  | solve by destruction 1 subst (Atom.atom_dec_eq a a0)
  | solve by destruction 2 subst (Atom.atom_dec_eq a a0) (IHe1 e2)  
  | solve by destruction 1 subst (Atom.atom_dec_eq a a0) 
  | solve by destruction 1 subst (eq_nat_dec n n0) ].
Case "exp_bool".
destruct b; destruct b0; try solve [left; reflexivity | right; congruence].
Case "exp_obj".
assert (l = l0 \/ l <> l0). 
  SCase "list proof".
  apply in_dec_dec_list. intros. rewrite Forall_forall in H. 
  remember a1 as a1'; destruct a1'. remember a2 as a2'; destruct a2'.
  assert (EqS := string_dec_eq s s0). inversion EqS; [auto | right; congruence].
  assert (e = e0 \/ e <> e0). apply H. apply in_split_r in H1. simpl in H1. 
  replace (map (snd (B:=exp)) l) with (snd (split l)). auto. symmetry; apply map_snd_snd_split.
  inversion H4; [left; subst; auto | right; congruence].
inversion H1; [left; subst; auto | right; congruence].
Qed.

Definition fieldnames l := map (@fst string exp) l.
Definition values l := map (@snd string exp) l.
Definition map_values A (f : exp -> A) l := 
  map (fun kv => ((@fst string exp) kv, f ((@snd string exp) kv))) l.
Hint Unfold values fieldnames map_values.

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
  | exp_catch e1 e2 => exp_catch (open_rec k u e1) (open_rec (S k) u e2)
  | exp_throw e     => exp_throw (open_rec k u e)
  | exp_seq e1 e2   => exp_seq (open_rec k u e1) (open_rec k u e2)
  | exp_finally e1 e2 => exp_finally (open_rec k u e1) (open_rec k u e2)
  | exp_obj l     => exp_obj (map_values (open_rec k u) l)
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
  | lc_set   : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_set e1 e2)
  | lc_catch : forall n e1 e2, 
      lc' n e1 -> lc' (S n) e2 -> lc' n (exp_catch e1 e2)
  | lc_throw : forall n e, lc' n e -> lc' n (exp_throw e)
  | lc_seq   : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_seq e1 e2)
  | lc_finally : forall n e1 e2, 
    lc' n e1 ->
    lc' n e2 ->
    lc' n (exp_finally e1 e2)
  | lc_obj   : forall n l, NoDup (fieldnames l) -> Forall (lc' n) (values l) -> lc' n (exp_obj l).

Reset lc'_ind.

Definition lc'_ind := fun (P : nat -> exp -> Prop)
  (f : forall (n : nat) (a : atom), P n (exp_fvar a))
  (f0 : forall k n : nat, k < n -> P n (exp_bvar k))
  (f1 : forall (n : nat) (e : exp),
        lc' (S n) e -> P (S n) e -> P n (exp_abs e))
  (f2 : forall (n : nat) (e1 e2 : exp),
        lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_app e1 e2))
  (f3 : forall n x : nat, P n (exp_nat x))
  (f4 : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_succ e))
  (f5 : forall (n : nat) (b : bool), P n (exp_bool b))
  (f6 : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_not e))
  (f7 : forall (n : nat) (e e1 e2 : exp),
        lc' n e ->
        P n e ->
        lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_if e e1 e2))
  (f8 : forall n : nat, P n exp_err)
  (f9 : forall (n : nat) (x : atom) (e : exp),
        lc' n e -> P n e -> P n (exp_label x e))
  (f10 : forall (n : nat) (x : atom) (e : exp),
         lc' n e -> P n e -> P n (exp_break x e))
  (f11 : forall (n : nat) (x : loc), P n (exp_loc x))
  (f12 : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_ref e))
  (f13 : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_deref e))
  (f14 : forall (n : nat) (e1 e2 : exp),
         lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_set e1 e2))
  (f15 : forall (n : nat) (e1 e2 : exp),
         lc' n e1 ->
         P n e1 -> lc' (S n) e2 -> P (S n) e2 -> P n (exp_catch e1 e2))
  (f16 : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_throw e))
  (f17 : forall (n : nat) (e1 e2 : exp),
         lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_seq e1 e2))
  (f18 : forall (n : nat) (e1 e2 : exp),
         lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_finally e1 e2))
  (f19 : forall (n : nat) (l : list (string * exp)),
         NoDup (fieldnames l) -> Forall (P n) (map (@snd string exp) l) -> P n (exp_obj l)) =>
fix lc'_ind' (n : nat) (e : exp) (l : lc' n e) {struct l} : P n e :=
  match l in (lc' n0 e0) return (P n0 e0) with
  | lc_fvar n0 a => f n0 a
  | lc_bvar k n0 l0 => f0 k n0 l0
  | lc_abs n0 e0 l0 => f1 n0 e0 l0 (lc'_ind' (S n0) e0 l0)
  | lc_app n0 e1 e2 l0 l1 => f2 n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_nat n0 x => f3 n0 x
  | lc_succ n0 e0 l0 => f4 n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_bool n0 b => f5 n0 b
  | lc_not n0 e0 l0 => f6 n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_if n0 e0 e1 e2 l0 l1 l2 =>
      f7 n0 e0 e1 e2 l0 (lc'_ind' n0 e0 l0) l1 (lc'_ind' n0 e1 l1) l2 (lc'_ind' n0 e2 l2)
  | lc_err n0 => f8 n0
  | lc_label n0 x e0 l0 => f9 n0 x e0 l0 (lc'_ind' n0 e0 l0)
  | lc_break n0 x e0 l0 => f10 n0 x e0 l0 (lc'_ind' n0 e0 l0)
  | lc_loc n0 x => f11 n0 x
  | lc_ref n0 e0 l0 => f12 n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_deref n0 e0 l0 => f13 n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_set n0 e1 e2 l0 l1 => f14 n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_catch n0 e1 e2 l0 l1 =>
      f15 n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' (S n0) e2 l1)
  | lc_throw n0 e0 l0 => f16 n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_seq n0 e1 e2 l0 l1 => f17 n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_finally n0 e1 e2 l0 l1 => f18 n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_obj n0 l0 n1 pf_lc' => f19 n0 l0 n1
      ((fix forall_lc_ind T (pf_lc : Forall (lc' n0) T) : Forall (P n0) T :=
        match pf_lc with
          | Forall_nil => Forall_nil (P n0)
          | Forall_cons t l' isVal rest => 
            Forall_cons (A:=exp) (P:=P n0) (l:=l') t (lc'_ind' n0 t isVal) (forall_lc_ind l' rest)
        end) (map (@snd string exp) l0) pf_lc')
  end.

Definition lc e := lc' 0 e.

Inductive val : exp -> Prop :=
  | val_abs  : forall e, lc (exp_abs e) -> val (exp_abs e)
  | val_nat  : forall n, val (exp_nat n)
  | val_fvar : forall a, val (exp_fvar a)
  | val_bool : forall b, val (exp_bool b)
  | val_loc  : forall l, val (exp_loc l)
  | val_obj  : forall l, Forall val (values l)
                     -> NoDup (fieldnames l)
                     -> val (exp_obj l).
Reset val_ind.

Definition val_ind := fun (P : exp -> Prop)
  (f : forall e : exp, lc (exp_abs e) -> P (exp_abs e))
  (f0 : forall n : nat, P (exp_nat n))
  (f1 : forall a : atom, P (exp_fvar a))
  (f2 : forall b : bool, P (exp_bool b))
  (f3 : forall l : loc, P (exp_loc l))
  (f4 : forall l : list (string * exp), Forall P (map (@snd string exp) l) ->
        NoDup (fieldnames l) -> P (exp_obj l))
  (e : exp) (v : val e) =>
  fix val_ind' (e : exp) (v : val e) { struct v } : P e :=
  match v in (val e0) return (P e0) with
    | val_abs x x0 => f x x0
    | val_nat x => f0 x
    | val_fvar x => f1 x
    | val_bool x => f2 x
    | val_loc x => f3 x
    | val_obj x pf_vals x0 => f4 x
      ((fix forall_val_ind T (pf_vals : Forall val T) : Forall P T :=
        match pf_vals with
          | Forall_nil => Forall_nil P
          | Forall_cons t l' isVal rest => 
            Forall_cons (A:=exp) (P:=P) (l:=l') t (val_ind' t isVal) (forall_val_ind l' rest)
        end) (map (@snd string exp) x) pf_vals) x0
  end.


Inductive stored_val : Set :=
  | val_with_proof : forall (v : exp), val v -> stored_val.

Definition sto := AtomEnv.t stored_val.

Inductive tag : Set :=
  | TagAbs  : tag
  | TagNat  : tag
  | TagVar  : tag
  | TagBool : tag
  | TagLoc  : tag
  | TagObj  : tag.

Inductive tagof : exp -> tag -> Prop :=
  | tag_abs  : forall e, tagof (exp_abs e) TagAbs
  | tag_nat  : forall n, tagof (exp_nat n) TagNat
  | tag_var  : forall x, tagof (exp_fvar x) TagVar
  | tag_bool : forall b, tagof (exp_bool b) TagBool
  | tag_loc  : forall l, tagof (exp_loc l) TagLoc
  | tag_obj  : forall l, tagof (exp_obj l) TagObj.

Hint Unfold open lc.
Hint Constructors lc'.

Lemma lc_val : forall v,
  val v -> lc' 0 v.
Proof with auto.
intros. induction v; try inversion H...
Case "exp_obj".
  constructor... subst... induction l; simpl... constructor.
  SCase "head".
  inversion H0. apply H5. subst. inversion H2. auto.  
  SCase "tail". 
  apply IHl. inversion H0... constructor. 
  inversion H2... inversion H2... inversion H3... inversion H2... inversion H3...
Qed.

Hint Resolve lc_val.

Lemma lc_ascend : forall k k' e, k' >= k -> lc' k e -> lc' k' e.
Proof with auto.
intros.
generalize dependent k'.
induction H0...
Case "lc_bvar".
  intros. apply lc_bvar. omega.
Case "lc_abs".
  intros. apply lc_abs. apply IHlc'. omega.
Case "lc_catch".
  intros. apply lc_catch... apply IHlc'2. omega.
Case "lc_obj".
  intros. apply lc_obj... unfold values.
  induction H0; constructor... 
Qed.
Hint Resolve lc_ascend.


Hint Constructors tagof tag.
Lemma decide_tagof : forall e t, tagof e t \/  ~ tagof e t.
Proof.
  intros.
  unfold not.
  destruct e; destruct t; try solve  [ auto | right; intros; inversion H ].
Qed.

Lemma dec_in : forall (l : list string) a, In a l \/ ~ In a l.
Proof with eauto.
induction l. intro; right; intro; inversion H.
intro. assert (dec := string_dec_eq a a0).
destruct dec; auto. inversion H.
 left; constructor...
 assert (H1 := IHl a0). inversion H1. left; right... 
 right. intro. apply H0. inversion H2... contradiction.
Qed.

Lemma dec_no_dup_strings : forall l : list string, NoDup l \/ ~ NoDup l. 
Proof with eauto.
induction l. left. constructor.
inversion IHl. assert (DecIn := dec_in l a).
inversion DecIn. right. intro. inversion H1. contradiction. left. constructor...
right. intro; inversion H0; contradiction.
Qed.

Ltac inverting_and_solve' e := 
  let D := fresh "D" in let Neq := fresh "Neq" in 
    assert (D := e); inversion D; [idtac | right; intro Neq; inversion Neq; contradiction].
Tactic Notation "solve" "by" "inverting" "1" tactic(t) constr(e) := inverting_and_solve' e; left; t; auto.
Tactic Notation "solve" "by" "inverting" "2" tactic(t) constr(e1) constr(e2) := 
  inverting_and_solve' e1; solve by inverting 1 (t) e2.
Tactic Notation "solve" "by" "inverting" "3" tactic(t) constr(e1) constr(e2) constr (e3) := 
  inverting_and_solve' e1; solve by inverting 2 (t) e2 e3.

Lemma decide_lc : forall e, forall n, lc' n e \/  ~ lc' n e.
Proof with eauto.
induction e; intro; try solve [ 
  left; auto
| solve by inverting 1 (constructor) (IHe n)
| solve by inverting 1 (constructor) (IHe (S n))
| solve by inverting 2 (constructor) (IHe1 n) (IHe2 n)
| solve by inverting 2 (constructor) (IHe1 n) (IHe2 (S n))
| solve by inverting 3 (constructor) (IHe1 n) (IHe2 n) (IHe3 n)
].
Case "exp_bvar".
intro. assert (decidable (n0 <= n)). apply Coq.Arith.Compare_dec.dec_le.
inversion H. right. intro. inversion H1. omega.
left. constructor. omega.
Case "exp_obj".
intro. assert (Forall (fun e => lc' n e \/ ~ lc' n e) (map (snd (B:=exp)) l)).
induction H. constructor. apply Forall_cons. apply H. apply IHForall.
eapply forall_dec_dec_forall in H0. inversion H0. 
assert (ND := dec_no_dup_strings (fieldnames l)).
inversion ND.
left. constructor. auto. unfold values... right; intro; apply H2. inversion H3...
right. intro. apply H1. inversion H2. apply H6.
Qed.


Lemma decide_val : forall e, val e \/ ~ val e.
Proof with eauto.
unfold not. intro. 
induction e; try solve [left; constructor | right; intro H; inversion H].
Case "exp_abs". 
induction IHe. left. constructor. constructor. apply lc_ascend with 0...
assert (lc' 1 e \/ ~ lc' 1 e). apply decide_lc.
inversion H0. left; constructor... right; intro. apply H1. inversion H2. inversion H4. auto.
Case "exp_obj".
apply (forall_dec_dec_forall val (l:=(map (@snd string exp) l))) in H.
inversion H. assert (H1 := dec_no_dup_strings (fieldnames l)).
inversion H1. left; constructor; unfold values; auto... right. intro. inversion H3. contradiction.
right. intro. inversion H1. contradiction.
Qed.


Inductive E : Set :=
  | E_hole    : E
  | E_app_1   : E -> exp -> E
  | E_app_2   : forall (v : exp), val v -> E -> E
  | E_succ    : E -> E
  | E_not     : E -> E
  | E_if      : E -> exp -> exp -> E
  | E_label   : atom -> E -> E
  | E_break   : atom -> E -> E
  | E_ref     : E -> E
  | E_deref   : E -> E
  | E_setref1 : E -> exp -> E
  | E_setref2 : forall (v : exp), val v -> E -> E
  | E_catch   : E -> exp -> E
  | E_throw   : E -> E
  | E_seq   : E -> exp -> E
  | E_finally  : E -> exp -> E
  | E_obj     : forall (vs : list (string * exp)) (es : list (string * exp)), 
                  (Forall val (values vs)) -> string -> E -> E.

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
  | redex_set  : forall v1 v2, val v1 -> val v2 -> pot_redex (exp_set v1 v2)
  | redex_catch : forall v e, val v -> lc' 1 e -> pot_redex (exp_catch v e)
  | redex_throw : forall v, val v -> pot_redex (exp_throw v)
  | redex_seq   : forall v e, val v -> lc e -> pot_redex (exp_seq v e)
  | redex_finally : forall v e, val v -> lc e -> pot_redex (exp_finally v e).

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
      decompose (exp_set e1 e2) (E_setref2 v1 E) ae
  | cxt_throw : forall e E ae,
      decompose e E ae ->
      decompose (exp_throw e) (E_throw E) ae
  | cxt_catch : forall e1 e2 E ae,
      decompose e1 E ae ->
      decompose (exp_catch e1 e2) (E_catch E e2) ae
  | cxt_seq : forall E e1 e2 ae,
      decompose e1 E ae ->
      decompose (exp_seq e1 e2) (E_seq E e2) ae
  | cxt_finally : forall E e1 e2 ae,
      decompose e1 E ae ->
      decompose (exp_finally e1 e2) (E_finally E e2) ae
  | cxt_obj  : forall vs es k e E e' (are_vals : Forall val (values vs)),
      decompose e E e' ->
      decompose (exp_obj (vs++(k,e)::es)) (E_obj vs es are_vals k E) e'.

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
      decompose1 (exp_set e1 e2) (E_setref2 v1 E_hole) e2
  | cxt1_throw : forall e,
      decompose1 (exp_throw e) (E_throw E_hole) e
  | cxt1_seq   : forall e1 e2,
      decompose1 (exp_seq e1 e2) (E_seq E_hole e2) e1
  | cxt1_obj  : forall vs es k e E (are_vals : Forall val (values vs)),
      decompose1 (exp_obj (vs++(k,e)::es)) (E_obj vs es are_vals k E) e.

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
  | E_catch cxt e2 => exp_catch (plug e cxt) e2
  | E_throw cxt    => exp_throw (plug e cxt)
  | E_seq cxt e2   => exp_seq (plug e cxt) e2
  | E_finally cxt e2 => exp_finally (plug e cxt) e2
  | E_obj vs es _ k cxt => exp_obj (vs++(k,plug e cxt)::es)
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
      contract e exp_err
  | contract_throw : forall v,
      val v ->
      contract (exp_throw v) exp_err (* TODO: errors need carry values *)
  | contract_catch_normal : forall v e,
      val v ->
      contract (exp_catch v e) v
  | contract_catch_catch : forall e,
      contract (exp_catch exp_err e) (open e (exp_nat 0)) (* TODO: err vals *)
  | contract_seq : forall e v,
      val v ->
      contract (exp_seq v e) e
  | contract_finally_normal : forall v e,
      val v ->
      contract (exp_finally v e) (exp_seq e v)
  | contract_finally_propagate_err : forall e ,
      contract (exp_finally exp_err e) (exp_seq e exp_err)
  | contract_finally_propagate_break : forall x v e,
      val v ->
      contract (exp_finally (exp_break x v) e) (exp_seq e (exp_break x v)).

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
    | Case_aux c "exp_set"
    | Case_aux c "exp_catch"
    | Case_aux c "exp_throw"
    | Case_aux c "exp_seq"
    | Case_aux c "exp_finally"
    | Case_aux c "exp_obj" ].
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
    | Case_aux c "lc_set"
    | Case_aux c "lc_catch"
    | Case_aux c "lc_throw"
    | Case_aux c "lc_seq"
    | Case_aux c "lc_finally"
    | Case_aux c "lc_obj" ].
Tactic Notation "val_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "val_abs"
    | Case_aux c "val_nat"
    | Case_aux c "val_fvar"
    | Case_aux c "val_bool"
    | Case_aux c "val_loc"
    | Case_aux c "val_obj" ].
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
    | Case_aux c "E_setref2"
    | Case_aux c "E_seq"
    | Case_aux c "E_finally"
    | Case_aux c "E_obj" ].
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
    | Case_aux c "redex_set"
    | Case_aux c "redex_throw"
    | Case_aux c "redex_catch"
    | Case_aux c "redex_seq"
    | Case_aux c "redex_finally" ].
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
    | Case_aux c "decompose_set2" 
    | Case_aux c "decompose_throw"
    | Case_aux c "decompose_catch"
    | Case_aux c "decompose_seq"
    | Case_aux c "decompose_finally"
    | Case_aux c "decompose_obj" ].
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
    | Case_aux c "decompose1_set2"
    | Case_aux c "decompose1_throw"
    | Case_aux c "decompose1_seq"
    | Case_aux c "decompose1_obj" ].
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
    | Case_aux c "contract_err_bubble"
    | Case_aux c "contract_throw"
    | Case_aux c "contract_catch_normal"
    | Case_aux c "contract_catch_catch"
    | Case_aux c "contract_seq"
    | Case_aux c "contract_finally_normal"
    | Case_aux c "contract_finally_propagate_err"
    | Case_aux c "contract_finally_propagate_break" ].
Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "step_err"
  | Case_aux c "step_contract"
  | Case_aux c "step_ref"
  | Case_aux c "step_deref"
  | Case_aux c "step_deref_err"
  | Case_aux c "step_setref"
  | Case_aux c "step_setref_err" ].

Hint Unfold values fieldnames map_values.
Hint Unfold open lc.
Hint Constructors lc'.
Hint Resolve lc_val.
Hint Resolve lc_ascend.
Hint Constructors tagof tag.
Hint Constructors decompose E val exp pot_redex exp val pot_redex contract
                  step decompose1 stored_val.

Lemma decompose_pot_redex : forall e E ae,
  decompose e E ae -> pot_redex ae.
Proof with auto. intros. induction H... Qed.

Lemma plug_ok : forall e E e',
  decompose e E e' -> plug e' E = e.
Proof.
intros. Print decompose.
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
Proof. intros. decompose_cases (induction H0) Case; try solve [inversion H; eauto | auto].
Case "decompose_obj".
  apply IHdecompose. apply Forall_in with (values (vs ++ (k, e) :: es)). simpl.
  unfold lc in H. inversion H. auto.
  unfold values; rewrite map_app; simpl; apply in_middle.
Qed.

Lemma decompose1_lc : forall E e ae,
  lc e ->
  decompose1 e E ae ->
  lc ae.
Proof. intros. decompose1_cases (induction H0) Case; try solve [inversion H; eauto | auto]. 
Case "decompose1_obj".
  apply Forall_in with (values (vs ++ (k, e) :: es)). inversion H. auto.
  unfold values. rewrite map_app. simpl.
  apply in_middle.
Qed.


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
Case "lc_obj".
  assert (forall x : string * exp, In x l -> decidable (val (snd x))). intros; apply decide_val.
  assert (Split := (take_while l (fun kv => val (snd kv)) H1)).
  inversion Split. 
  SCase "Everything in (exp_obj l) is already a value".
    left. constructor... unfold values; rewrite map_snd_snd_split. apply forall_snd_comm...
  SCase "Something in (exp_obj l) is not yet a value".
    right. inversion H2; clear H2. inversion H3; clear H3. 
    inversion H2; clear H2. inversion H3; clear H3. inversion H4; clear H4.
    remember x1 as x1'; destruct x1'.
    assert (Forall val (values x)). unfold values; rewrite map_snd_snd_split; apply forall_snd_comm...
    assert (val e \/ (exists E ae, decompose e E ae)).   
      assert (Forall (fun e => val e \/ exists E ae, decompose e E ae) (map (snd (B:=exp)) l)). 
      induction H0; constructor. apply H0... auto. clear H0.
      rewrite Forall_forall in H6. apply H6.  rewrite map_snd_snd_split. rewrite H2.
      rewrite snd_split_comm. simpl. apply in_middle. 
    simpl in H5. inversion H6. contradiction. 
    inversion H7. inversion H8. exists (E_obj x x0 H4 s x2). exists x3. 
    rewrite H2. apply cxt_obj...
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
Proof with auto.
intros.
decompose_cases (induction H1) Case;
 first [ inversion H; subst; simpl; unfold lc in *; constructor ; try solve_lc_plug; auto | auto ]. 
Case "decompose_obj".
  SCase "Proving NoDup of fieldnames after plugging".
  unfold fieldnames in *. rewrite map_fst_fst_split. rewrite fst_split_comm. simpl.
  rewrite map_fst_fst_split in H3; rewrite fst_split_comm in H3; simpl in H3...
  SCase "Proving all are values after plugging".
  unfold values in *. rewrite map_snd_snd_split; rewrite snd_split_comm; simpl.
  rewrite map_snd_snd_split in H5; rewrite snd_split_comm in H5; simpl in H5...
  rewrite forall_app. rewrite forall_app in H5. inversion H5. split... inversion H4... 
Qed.

Hint Resolve lc_plug.


Lemma lc_active : forall e,
  pot_redex e -> lc e.
Proof. intros. unfold lc. inversion H; constructor; eauto using lc_val. Qed.

Hint Resolve lc_active.

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
Case "exp_obj".
  simpl. unfold map_values. apply forall_map_comm in H. constructor. 
  SCase "NoDup". 
    inversion H1. unfold fieldnames in *. rewrite map_fst_fst_split in *.
    rewrite fst_split_map_snd...
  SCase "values". 
    unfold values. apply forall_map_comm. apply forall_map_comm. simpl. 
    rewrite Forall_forall. rewrite Forall_forall in H.
    intros. apply H... inversion H1. rewrite Forall_forall in H6. apply H6. 
    destruct x as (s, e). subst. unfold values. rewrite map_snd_snd_split. apply in_split_r...
Qed.

Lemma lc_contract : forall ae e,
  lc ae ->
  contract ae e ->
  lc e.
Proof with auto.
intros.
contract_cases (destruct H0) Case; try solve [auto | inversion H; auto].
Case "contract_succ". simpl. exp_cases (destruct e) SCase; auto.
Case "contract_not". simpl. exp_cases (destruct e) SCase; auto.
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
Case "contract_catch_catch".
  unfold lc in *.
  inversion H; subst.
  unfold open.
  apply lc_open...
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
