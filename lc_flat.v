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

Parameter __proto__ : string.


Section ListLemmas.


Fixpoint lookup_assoc A B (l : list (A * B)) k default (eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) : B
  := match l with
       | [] => default
       | (k',v)::tl => if (eq_dec k k') then v else lookup_assoc tl k default eq_dec
     end.
Fixpoint update_assoc A B (l : list (A * B)) k v (eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) : list (A*B)
  := match l with
       | [] => []
       | (k',o)::tl => if (eq_dec k k') then (k',v)::tl else (k',o)::(update_assoc tl k v eq_dec)
     end.
Fixpoint remove_fst A B (x : A) (l : list (A*B)) (eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}): list (A*B) :=
    match l with
      | [] => []
      | (y,b)::tl => if (eq_dec x y) then remove_fst x tl eq_dec else (y,b)::(remove_fst x tl eq_dec)
    end.

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

Lemma remove_fst_in : forall A B (a : A) (b : B) (l : list (A*B)) eq_dec, ~ In (a,b) (remove_fst a l eq_dec).
Proof with eauto.
  induction l. simpl...
  intros. destruct a0 as (xa, xb). simpl. destruct (eq_dec a xa). apply IHl.
  simpl. intro. inversion H. inversion H0. symmetry in H2; contradiction. apply (IHl eq_dec H0).
Qed.
Lemma remove_fst_in_pair : forall A B a (l : list (A*B)) eq_dec, ~ In a (fst (split (remove_fst a l eq_dec))).
Proof with eauto.
  intros. induction l; simpl... intro. apply IHl. destruct a0 as (aa, ab). destruct (eq_dec a aa); simpl...
  simpl in H. rewrite (split_components (remove_fst a l eq_dec)) in H. simpl in H.
  inversion H. symmetry in H0; contradiction. auto.
Qed.
Lemma still_not_in : forall A B s (l:list(A*B)) eq_dec, ~ In s (map (@fst A B) l) -> ~ In s (map (@fst A B) (remove_fst s l eq_dec)).
Proof with auto. induction l; simpl...
  intros; intro. destruct a as (aa, ab). simpl in *.
  assert (aa <> s /\ ~ In s (map (@fst A B) l)). split. intro; apply H; left... intro; apply H; right...
  clear H. inversion_clear H1. destruct (eq_dec s aa). symmetry in e; contradiction. 
  inversion H0. simpl in H1; contradiction. unfold not in IHl. apply IHl with eq_dec. intro. contradiction. auto.
Qed.
Theorem in_split_fst : forall A B a (l:list (A*B)), In a (fst (split l)) -> exists l1, exists l2, exists b, l = l1++(a,b)::l2.
Proof.
  induction l; intros; simpl... inversion H. destruct a0 as (xa, xb). rewrite fst_split_cons in H.
  inversion H. exists []; exists l; exists xb... subst; simpl; reflexivity.
  clear H. assert (H := IHl H0). inversion_clear H. inversion_clear H1. inversion_clear H. 
  exists ((xa,xb)::x); exists x0; exists x1. subst; simpl. reflexivity.
Qed.

  Lemma remove_app_comm : forall A B l1 (f:A) (x:B) l2 eq_dec, 
    remove_fst f (l1 ++ (f, x) :: l2) eq_dec = remove_fst f l1 eq_dec ++ remove_fst f [(f,x)] eq_dec ++ remove_fst f l2 eq_dec.
    Proof with auto. induction l1. simpl... intros. destruct (eq_dec f f)... intros.
      destruct a as (aa, ab). remember ((f, x) :: l2) as temp. simpl.
      destruct (eq_dec f aa). rewrite Heqtemp; apply IHl1. rewrite <- app_comm_cons.
      f_equal. subst. apply IHl1. 
    Qed.
Lemma fst_split_comm2 : forall A B (l1 : list(A*B)) l2, 
  fst (split (l1 ++ l2)) = fst (split l1) ++ fst (split l2).
Proof with eauto.
  induction l1; intros. simpl...
  simpl.
  destruct a as (a0, b0). rewrite (split_components l1); rewrite (split_components l2); 
  rewrite (split_components (l1 ++ l2)); simpl. f_equal...
Qed.
Lemma not_in_remove_eq : forall A B f (l: list (A*B)) eq_dec, ~ In f (fst (split l)) -> l = remove_fst f l eq_dec.
Proof with eauto.
  induction l. intros. simpl...
  intros. destruct a as (s, e). simpl in H. rewrite (split_components l) in H; simpl in H.
  assert (s <> f). intro; apply H; left... assert (~ In f (fst (split l))). intro; apply H; right...
  clear H. assert (H := IHl eq_dec H1). simpl. destruct (eq_dec f s). symmetry in e0; contradiction.
  f_equal...
Qed.
Lemma snd_split_comm2 : forall A B (l1 : list(A*B)) l2, 
  snd (split (l1 ++ l2)) = snd (split l1) ++ snd (split l2).
Proof with eauto.
  induction l1; intros. simpl...
  simpl.
  destruct a as (a0, b0). rewrite (split_components l1); rewrite (split_components l2); 
  rewrite (split_components (l1 ++ l2)); simpl. f_equal...
Qed.
Lemma update_fieldnames_eq : forall A B (l:list(A*B)) f v eq_dec, map (@fst A B) l = map (@fst A B) (update_assoc l f v eq_dec).
Proof. induction l; intros; auto...
  destruct a as (s,e). simpl. destruct (eq_dec f s); f_equal; simpl. auto. f_equal; apply IHl.
Qed.
Lemma update_values_eq : forall A B l f v P eq_dec, Forall P (map (@snd A B) l) -> P v -> Forall P (map (@snd A B) (update_assoc l f v eq_dec)).
Proof with auto. induction l; intros; simpl; auto. intros.
  destruct a as (s, e). destruct (eq_dec f s). simpl. constructor... inversion H...
  constructor. inversion H... simpl in H. apply IHl. inversion H... auto.
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
  | exp_string : string -> exp
  | exp_undef : exp
  | exp_null  : exp
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
  | exp_obj   : list (string * exp) -> exp
  | exp_getfield : exp -> string -> exp
  | exp_setfield : exp -> string -> exp -> exp
  | exp_delfield : exp -> string -> exp.
Reset exp_ind.

Definition exp_ind := fun (P : exp -> Prop)
  (rec_exp_fvar : forall a : atom, P (exp_fvar a))
  (rec_exp_bvar : forall n : nat, P (exp_bvar n))
  (rec_exp_abs : forall e : exp, P e -> P (exp_abs e))
  (rec_exp_app : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_app e e0))
  (rec_exp_nat : forall n : nat, P (exp_nat n))
  (rec_exp_succ : forall e : exp, P e -> P (exp_succ e))
  (rec_exp_bool : forall b : bool, P (exp_bool b))
  (rec_exp_string : forall s : string, P (exp_string s))
  (rec_exp_undef : P exp_undef)
  (rec_exp_null : P exp_null)
  (rec_exp_not : forall e : exp, P e -> P (exp_not e))
  (rec_exp_if : forall e : exp, P e -> forall e0 : exp, P e0 -> forall e1 : exp, P e1 -> P (exp_if e e0 e1))
  (rec_exp_err : P exp_err)
  (rec_exp_label : forall (a : atom) (e : exp), P e -> P (exp_label a e))
  (rec_exp_break : forall (a : atom) (e : exp), P e -> P (exp_break a e))
  (rec_exp_loc : forall l : loc, P (exp_loc l))
  (rec_exp_deref : forall e : exp, P e -> P (exp_deref e))
  (rec_exp_ref : forall e : exp, P e -> P (exp_ref e))
  (rec_exp_set : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_set e e0))
  (rec_exp_catch : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_catch e e0))
  (rec_exp_throw : forall e : exp, P e -> P (exp_throw e))
  (rec_exp_seq : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_seq e e0))
  (rec_exp_finally : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_finally e e0))
  (rec_exp_obj : forall l : list (string * exp), Forall P (map (@snd string exp) l) -> P (exp_obj l))
  (rec_exp_getfield : forall o : exp, P o -> forall f : string, P (exp_getfield o f))
  (rec_exp_setfield : forall o : exp, P o -> forall (f : string) (e : exp), P e -> P (exp_setfield o f e))
  (rec_exp_delfield : forall o : exp, P o -> forall f : string, P (exp_delfield o f))
  =>
fix exp_rec' (e : exp) {struct e} : P e :=
  match e as e0 return (P e0) with
  | exp_fvar a => rec_exp_fvar a
  | exp_bvar n => rec_exp_bvar n
  | exp_abs e0 => rec_exp_abs e0 (exp_rec' e0)
  | exp_app e0 e1 => rec_exp_app e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_nat n => rec_exp_nat n
  | exp_succ e0 => rec_exp_succ e0 (exp_rec' e0)
  | exp_bool b => rec_exp_bool b
  | exp_string s => rec_exp_string s
  | exp_undef => rec_exp_undef
  | exp_null => rec_exp_null
  | exp_not e0 => rec_exp_not e0 (exp_rec' e0)
  | exp_if e0 e1 e2 => rec_exp_if e0 (exp_rec' e0) e1 (exp_rec' e1) e2 (exp_rec' e2)
  | exp_err => rec_exp_err
  | exp_label a e0 => rec_exp_label a e0 (exp_rec' e0)
  | exp_break a e0 => rec_exp_break a e0 (exp_rec' e0)
  | exp_loc l => rec_exp_loc l
  | exp_deref e0 => rec_exp_deref e0 (exp_rec' e0)
  | exp_ref e0 => rec_exp_ref e0 (exp_rec' e0)
  | exp_set e0 e1 => rec_exp_set e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_catch e0 e1 => rec_exp_catch e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_throw e0 => rec_exp_throw e0 (exp_rec' e0)
  | exp_seq e0 e1 => rec_exp_seq e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_finally e0 e1 => rec_exp_finally e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_obj l =>
    rec_exp_obj l ((fix forall_rec (ls : list (string * exp)) : Forall P (map (@snd string exp) ls) :=
      match ls with
        | nil => Forall_nil P
        | (_,tr)::rest => Forall_cons tr (exp_rec' tr) (forall_rec rest)
      end) l)
  | exp_getfield o f => rec_exp_getfield o (exp_rec' o) f
  | exp_setfield o f e => rec_exp_setfield o (exp_rec' o) f e (exp_rec' e)
  | exp_delfield o f => rec_exp_delfield o (exp_rec' o) f
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
  | solve by destruction 1 subst (string_dec_eq s s0)
  | solve by destruction 1 subst (IHe1 e2)
  | solve by destruction 2 subst (IHe1_1 e2_1) (IHe1_2 e2_2)
  | solve by destruction 3 subst (IHe1_1 e2_1) (IHe1_2 e2_2) (IHe1_3 e2_3)
  | solve by destruction 1 subst (Atom.atom_dec_eq a a0)
  | solve by destruction 1 subst (Atom.atom_dec_eq l l0)
  | solve by destruction 2 subst (Atom.atom_dec_eq a a0) (IHe1 e2)  
  | solve by destruction 1 subst (eq_nat_dec n n0) 
  | solve by destruction 2 subst (IHe1 e2) (string_dec_eq f f0)
  | solve by destruction 3 subst (IHe1_1 e2_1) (IHe1_2 e2_2) (string_dec_eq f f0) ].
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

Lemma str_exp_eq_dec : forall (a1 a2 : (string * exp)), a1 = a2 \/ a1 <> a2.
Proof with auto.
  destruct a1 as (a1s, a1e); destruct a2 as (a2s, a2e).
  assert (S := string_dec_eq a1s a2s). assert (E := exp_eq_dec a1e a2e).
  destruct S; destruct E; subst; solve [left; auto | right; congruence].
Qed.

Lemma str_exp_list_eq_dec : forall (l1 l2 : list (string * exp)), l1 = l2 \/ l1 <> l2.
Proof.
  induction l1. intros; destruct l2; solve [left; auto | right; congruence].
  intros. destruct l2. right; congruence.
  assert (E := str_exp_eq_dec a p). destruct E.
  destruct (IHl1 l2); subst; solve [left; auto | right; congruence].
  right; congruence.
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
  | exp_string s   => e
  | exp_undef      => e
  | exp_null       => e
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
  | exp_getfield o f => exp_getfield (open_rec k u o) f
  | exp_setfield o f e => exp_setfield (open_rec k u o) f (open_rec k u e)
  | exp_delfield o f => exp_delfield (open_rec k u o) f
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
  | lc_string : forall n s, lc' n (exp_string s)
  | lc_undef : forall n, lc' n exp_undef
  | lc_null : forall n, lc' n exp_null
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
  | lc_obj   : forall n l, NoDup (fieldnames l) -> Forall (lc' n) (values l) -> lc' n (exp_obj l)
  | lc_getfield : forall n o f, lc' n o -> lc' n (exp_getfield o f)
  | lc_setfield : forall n o f e, lc' n o -> lc' n e -> lc' n (exp_setfield o f e)
  | lc_delfield : forall n o f, lc' n o -> lc' n (exp_delfield o f)
.

Reset lc'_ind.

Definition lc'_ind := fun (P : nat -> exp -> Prop)
  (rec_lc_fvar : forall (n : nat) (a : atom), P n (exp_fvar a))
  (rec_lc_bvar : forall k n : nat, k < n -> P n (exp_bvar k))
  (rec_lc_abs : forall (n : nat) (e : exp),
        lc' (S n) e -> P (S n) e -> P n (exp_abs e))
  (rec_lc_app : forall (n : nat) (e1 e2 : exp),
        lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_app e1 e2))
  (rec_lc_nat : forall n x : nat, P n (exp_nat x))
  (rec_lc_succ : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_succ e))
  (rec_lc_bool : forall (n : nat) (b : bool), P n (exp_bool b))
  (rec_lc_string : forall (n : nat) (s : string), P n (exp_string s))
  (rec_lc_undef : forall n : nat, P n exp_undef)
  (rec_lc_null : forall n : nat, P n exp_null)
  (rec_lc_not : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_not e))
  (rec_lc_if : forall (n : nat) (e e1 e2 : exp),
        lc' n e ->
        P n e ->
        lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_if e e1 e2))
  (rec_lc_err : forall n : nat, P n exp_err)
  (rec_lc_label : forall (n : nat) (x : atom) (e : exp),
        lc' n e -> P n e -> P n (exp_label x e))
  (rec_lc_break : forall (n : nat) (x : atom) (e : exp),
         lc' n e -> P n e -> P n (exp_break x e))
  (rec_lc_loc : forall (n : nat) (x : loc), P n (exp_loc x))
  (rec_lc_ref : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_ref e))
  (rec_lc_deref : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_deref e))
  (rec_lc_set : forall (n : nat) (e1 e2 : exp),
         lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_set e1 e2))
  (rec_lc_catch : forall (n : nat) (e1 e2 : exp),
         lc' n e1 ->
         P n e1 -> lc' (S n) e2 -> P (S n) e2 -> P n (exp_catch e1 e2))
  (rec_lc_throw : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_throw e))
  (rec_lc_seq : forall (n : nat) (e1 e2 : exp),
         lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_seq e1 e2))
  (rec_lc_finally : forall (n : nat) (e1 e2 : exp),
         lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_finally e1 e2))
  (rec_lc_obj : forall (n : nat) (l : list (string * exp)),
         NoDup (fieldnames l) -> Forall (P n) (map (@snd string exp) l) -> P n (exp_obj l)) 
  (rec_lc_getfield : forall (n : nat) (o : exp), P n o -> forall f : string, P n (exp_getfield o f))
  (rec_lc_setfield : forall (n : nat) (o : exp), P n o -> forall (f : string) (e : exp), P n e -> P n (exp_setfield o f e))
  (rec_lc_delfield : forall (n : nat) (o : exp), P n o -> forall f : string, P n (exp_delfield o f))
=>
fix lc'_ind' (n : nat) (e : exp) (l : lc' n e) {struct l} : P n e :=
  match l in (lc' n0 e0) return (P n0 e0) with
  | lc_fvar n0 a => rec_lc_fvar n0 a
  | lc_bvar k n0 l0 => rec_lc_bvar k n0 l0
  | lc_abs n0 e0 l0 => rec_lc_abs n0 e0 l0 (lc'_ind' (S n0) e0 l0)
  | lc_app n0 e1 e2 l0 l1 => rec_lc_app n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_nat n0 x => rec_lc_nat n0 x
  | lc_succ n0 e0 l0 => rec_lc_succ n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_bool n0 b => rec_lc_bool n0 b
  | lc_string n0 s => rec_lc_string n0 s
  | lc_undef n0 => rec_lc_undef n0
  | lc_null n0 => rec_lc_null n0
  | lc_not n0 e0 l0 => rec_lc_not n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_if n0 e0 e1 e2 l0 l1 l2 =>
      rec_lc_if  n0 e0 e1 e2 l0 (lc'_ind' n0 e0 l0) l1 (lc'_ind' n0 e1 l1) l2 (lc'_ind' n0 e2 l2)
  | lc_err n0 => rec_lc_err n0
  | lc_label n0 x e0 l0 => rec_lc_label n0 x e0 l0 (lc'_ind' n0 e0 l0)
  | lc_break n0 x e0 l0 => rec_lc_break n0 x e0 l0 (lc'_ind' n0 e0 l0)
  | lc_loc n0 x => rec_lc_loc n0 x
  | lc_ref n0 e0 l0 => rec_lc_ref n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_deref n0 e0 l0 => rec_lc_deref n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_set n0 e1 e2 l0 l1 => rec_lc_set n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_catch n0 e1 e2 l0 l1 =>
      rec_lc_catch n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' (S n0) e2 l1)
  | lc_throw n0 e0 l0 => rec_lc_throw n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_seq n0 e1 e2 l0 l1 => rec_lc_seq n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_finally n0 e1 e2 l0 l1 => rec_lc_finally n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_obj n0 l0 n1 pf_lc' => rec_lc_obj n0 l0 n1
      ((fix forall_lc_ind T (pf_lc : Forall (lc' n0) T) : Forall (P n0) T :=
        match pf_lc with
          | Forall_nil => Forall_nil (P n0)
          | Forall_cons t l' isVal rest => 
            Forall_cons (A:=exp) (P:=P n0) (l:=l') t (lc'_ind' n0 t isVal) (forall_lc_ind l' rest)
        end) (map (@snd string exp) l0) pf_lc')
  | lc_getfield n0 o f lc_o  => rec_lc_getfield n0 o (lc'_ind' n0 o lc_o) f
  | lc_setfield n0 o f e lc_o lc_e => rec_lc_setfield n0 o (lc'_ind' n0 o lc_o) f e (lc'_ind' n0 e lc_e)
  | lc_delfield n0 o f lc_o => rec_lc_delfield n0 o (lc'_ind' n0 o lc_o) f
  end.

Definition lc e := lc' 0 e.

Inductive val : exp -> Prop :=
  | val_abs  : forall e, lc (exp_abs e) -> val (exp_abs e)
  | val_nat  : forall n, val (exp_nat n)
  | val_fvar : forall a, val (exp_fvar a)
  | val_bool : forall b, val (exp_bool b)
  | val_string : forall s, val (exp_string s)
  | val_undef : val (exp_undef)
  | val_null : val (exp_null)
  | val_loc  : forall l, val (exp_loc l)
  | val_obj  : forall l, Forall val (values l)
                     -> NoDup (fieldnames l)
                     -> val (exp_obj l).
Reset val_ind.

Definition val_ind := fun (P : exp -> Prop)
  (rec_val_abs : forall e : exp, lc (exp_abs e) -> P (exp_abs e))
  (rec_val_nat : forall n : nat, P (exp_nat n))
  (rec_val_fvar : forall a : atom, P (exp_fvar a))
  (rec_val_bool : forall b : bool, P (exp_bool b))
  (rec_val_string : forall s : string, P (exp_string s))
  (rec_val_undef : P exp_undef)
  (rec_val_null : P exp_null)
  (rec_val_loc : forall l : loc, P (exp_loc l))
  (rec_val_obj : forall l : list (string * exp), Forall P (map (@snd string exp) l) ->
        NoDup (fieldnames l) -> P (exp_obj l))
  (e : exp) (v : val e) =>
  fix val_ind' (e : exp) (v : val e) { struct v } : P e :=
  match v in (val e0) return (P e0) with
    | val_abs x x0 => rec_val_abs x x0
    | val_nat x => rec_val_nat x
    | val_fvar x => rec_val_fvar x
    | val_bool x => rec_val_bool x
    | val_string x => rec_val_string x
    | val_undef => rec_val_undef
    | val_null => rec_val_null
    | val_loc x => rec_val_loc x
    | val_obj x pf_vals x0 => rec_val_obj x
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
  | TagString : tag
  | TagUndef : tag
  | TagNull : tag
  | TagLoc  : tag
  | TagObj  : tag.

Inductive tagof : exp -> tag -> Prop :=
  | tag_abs  : forall e, tagof (exp_abs e) TagAbs
  | tag_nat  : forall n, tagof (exp_nat n) TagNat
  | tag_var  : forall x, tagof (exp_fvar x) TagVar
  | tag_bool : forall b, tagof (exp_bool b) TagBool
  | tag_string : forall s, tagof (exp_string s) TagString
  | tag_undef : tagof (exp_undef) TagUndef
  | tag_null : tagof (exp_null) TagNull
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
  destruct (dec_le n0 n). 
  right. intro. inversion H0. omega.
  left. constructor. omega.
Case "exp_obj".
  assert (Forall (fun e => lc' n e \/ ~ lc' n e) (map (snd (B:=exp)) l)).
    induction H. constructor. apply Forall_cons. apply H. apply IHForall.
  apply forall_dec_dec_forall in H0. inversion H0. 
  SCase "Everything in l is locally closed".
    destruct (dec_no_dup_strings (fieldnames l)).
    SSCase "Field names are distinct". left. constructor. auto. unfold values... 
    SSCase "Field names are not distinct". right; intro; apply H2. inversion H3...
  SCase "Not everything in l is locally closed". right. intro. apply H1. inversion H2. apply H6.
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
                  (Forall val (values vs)) -> string -> E -> E
  | E_getfield : E -> string -> E
  | E_setfield1 : E -> string -> exp -> E
  | E_setfield2 : forall (v : exp), val v -> string -> E -> E
  | E_delfield : E -> string -> E
.

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
  | redex_finally : forall v e, val v -> lc e -> pot_redex (exp_finally v e)
  | redex_getfield : forall o f, val o -> pot_redex (exp_getfield o f)
  | redex_setfield : forall o f e, val o -> val e -> pot_redex (exp_setfield o f e)
  | redex_delfield : forall o f, val o -> pot_redex (exp_delfield o f)
.

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
      decompose (exp_obj (vs++(k,e)::es)) (E_obj vs es are_vals k E) e'
  | cxt_getfield : forall o f E ae,
      decompose o E ae ->
      decompose (exp_getfield o f) (E_getfield E f) ae
  | cxt_setfield1 : forall o f e E ae,
      decompose o E ae ->
      decompose (exp_setfield o f e) (E_setfield1 E f e) ae
  | cxt_setfield2 : forall o f e E ae (v: val o),
      decompose e E ae ->
      decompose (exp_setfield o f e) (E_setfield2 v f E) ae
  | cxt_delfield : forall o f E ae,
      decompose o E ae ->
      decompose (exp_delfield o f) (E_delfield E f) ae
.

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
      decompose1 (exp_obj (vs++(k,e)::es)) (E_obj vs es are_vals k E) e
  | cxt1_getfield : forall o f,
      decompose1 (exp_getfield o f) (E_getfield E_hole f) o
  | cxt1_setfield1 : forall o f e,
      decompose1 (exp_setfield o f e) (E_setfield1 E_hole f e) o
  | cxt1_setfield2 : forall o f e (v : val o),
      decompose1 (exp_setfield o f e) (E_setfield2 v f E_hole) e
  | cxt1_delfield : forall o f,
      decompose1 (exp_delfield o f) (E_delfield E_hole f) o
.

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
  | E_getfield cxt f => exp_getfield (plug e cxt) f
  | E_setfield1 cxt f e' => exp_setfield (plug e cxt) f e'
  | E_setfield2 v _ f cxt => exp_setfield v f (plug e cxt)
  | E_delfield cxt f => exp_delfield (plug e cxt) f
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
      contract (exp_finally (exp_break x v) e) (exp_seq e (exp_break x v))
  | contract_getfield : forall l f,
      val (exp_obj l) ->
      In f (fieldnames l) ->
      contract (exp_getfield (exp_obj l) f) (lookup_assoc l f exp_err string_eq_dec)
  | contract_getfield_notfound : forall l f,
      val (exp_obj l) ->
      ~ In f (fieldnames l) -> ~ In __proto__ (fieldnames l) ->
      contract (exp_getfield (exp_obj l) f) exp_undef
  | contract_getfield_proto : forall l f,
      val (exp_obj l) ->
      ~ In f (fieldnames l) ->
      In __proto__ (fieldnames l) ->
      contract (exp_getfield (exp_obj l) f) 
        (exp_getfield (exp_deref (exp_getfield (exp_obj l) __proto__)) f)
  | contract_getfield_err : forall v f,
      val v -> ~ tagof v TagObj -> contract (exp_getfield v f) exp_err
  | contract_setfield_update : forall l f v,
      val (exp_obj l) ->
      val v ->
      In f (fieldnames l) ->
      contract (exp_setfield (exp_obj l) f v) (exp_obj (update_assoc l f v string_eq_dec))
  | contract_setfield_add : forall l f v,
      val (exp_obj l) ->
      val v ->
      ~ In f (fieldnames l) ->
      contract (exp_setfield (exp_obj l) f v) (exp_obj ((f,v)::l))
  | contract_setfield_err : forall v f v',
      val v -> ~ tagof v TagObj ->
      contract (exp_setfield v f v') exp_err
  | contract_delfield : forall l f,
      val (exp_obj l) ->
      In f (fieldnames l) ->
      contract (exp_delfield (exp_obj l) f) 
        (exp_obj (remove_fst f l string_eq_dec))
  | contract_delfield_notfound : forall l f,
      val (exp_obj l) ->
      ~ In f (fieldnames l) ->
      contract (exp_delfield (exp_obj l) f) (exp_obj l)
  | contract_delfield_err : forall v f,
      val v ->
      ~ tagof v TagObj ->
      contract (exp_delfield v f) exp_err
.

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
    | Case_aux c "exp_string"
    | Case_aux c "exp_undef"
    | Case_aux c "exp_null"
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
    | Case_aux c "exp_obj"
    | Case_aux c "exp_getfield"
    | Case_aux c "exp_setfield"
    | Case_aux c "exp_delfield"
 ].
Tactic Notation "lc_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "lc_fvar"
    | Case_aux c "lc_bvar"
    | Case_aux c "lc_abs"
    | Case_aux c "lc_app"
    | Case_aux c "lc_nat"
    | Case_aux c "lc_succ"
    | Case_aux c "lc_bool"
    | Case_aux c "lc_string"
    | Case_aux c "lc_undef"
    | Case_aux c "lc_null"
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
    | Case_aux c "lc_obj" 
    | Case_aux c "lc_getfield"
    | Case_aux c "lc_setfield"
    | Case_aux c "lc_delfield"
].
Tactic Notation "val_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "val_abs"
    | Case_aux c "val_nat"
    | Case_aux c "val_fvar"
    | Case_aux c "val_bool"
    | Case_aux c "val_string"
    | Case_aux c "val_undef"
    | Case_aux c "val_null"
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
    | Case_aux c "E_obj"
    | Case_aux c "E_getfield"
    | Case_aux c "E_setfield1"
    | Case_aux c "E_setfield2"
    | Case_aux c "E_delfield"
 ].
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
    | Case_aux c "redex_finally" 
    | Case_aux c "redex_getfield"
    | Case_aux c "redex_setfield"
    | Case_aux c "redex_delfield"
].
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
    | Case_aux c "decompose_obj" 
    | Case_aux c "decompose_getfield" 
    | Case_aux c "decompose_setfield1" 
    | Case_aux c "decompose_setfield2" 
    | Case_aux c "decompose_delfield" 
].
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
    | Case_aux c "decompose1_obj" 
    | Case_aux c "decompose1_getfield" 
    | Case_aux c "decompose1_setfield1" 
    | Case_aux c "decompose1_setfield2" 
    | Case_aux c "decompose1_delfield" 
].
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
    | Case_aux c "contract_finally_propagate_break" 
    | Case_aux c "contract_getfield"
    | Case_aux c "contract_getfield_notfound"
    | Case_aux c "contract_getfield_proto"
    | Case_aux c "contract_getfield_err"
    | Case_aux c "contract_setfield_update"
    | Case_aux c "contract_setfield_add"
    | Case_aux c "contract_setfield_err"
    | Case_aux c "contract_delfield"
    | Case_aux c "contract_delfield_notfound"
    | Case_aux c "contract_delfield_err"
].
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

Lemma decompose_not_val : forall e E ae,
  decompose e E ae -> ~ val e.
Proof with auto. intros. 
  decompose_cases (induction H) Case; try solve [inversion H; intro D; inversion D].
  Case "decompose_obj".
  intro. inversion H0. rewrite Forall_forall in H2. apply IHdecompose. apply H2.
  unfold values. rewrite map_app. simpl. apply in_middle.
Qed.



Lemma val_injective : forall e1 e2, e1 = e2 -> (val e1 <-> val e2).
Proof with eauto. intros; subst... tauto. Qed.

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
  | [ |- _ ] => fail "solve_decomp couldn't find hypothesis of shape '0 = 0 -> _'"
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
Case "lc_getfield". 
  destruct (IHlc' (eq_refl 0)); right.
    exists E_hole; exists (exp_getfield o f). constructor... 
    inversion H. inversion H0. exists (E_getfield x f); exists x0. constructor...
Case "lc_setfield".
  destruct (IHlc' (eq_refl 0)); [destruct (IHlc'0 (eq_refl 0)); right | right].
    exists E_hole; exists (exp_setfield o f e). constructor...
    inversion H0; inversion H1. exists (E_setfield2 H f x); exists x0. constructor...
    inversion H; inversion H0. exists (E_setfield1 x f e); exists x0. constructor...
Case "lc_delfield".
  destruct (IHlc' (eq_refl 0)); right.
    exists E_hole; exists (exp_delfield o f). constructor... 
    inversion H. inversion H0. exists (E_delfield x f); exists x0. constructor...
Qed.

(* NOTE: This doesn't work, but it's "right in principle".  
   It relies on proof equality, rather than equivalence, which is why it fails.

Lemma val_unique : forall e (p1 p2 : val e), p1 = p2.
exp_cases (induction e) Case; try solve [intros; inversion p1].
Admitted.
Hint Resolve val_unique.

Lemma decomp_unique : forall e E1 E2 ae1 ae2, 
  decompose e E1 ae1 -> decompose e E2 ae2 -> E1 = E2 /\ ae1 = ae2.
Proof with eauto.
exp_cases (induction e) Case; intros;
  try (match goal with [ H1 : decompose _ _ _, H2 : decompose _ _ _ |- _ ] => 
         inversion H1; inversion H2; auto end);
  try match goal with
        | [ H2 : decompose ?e _ _, H1 : pot_redex ?e |- _ ] =>
          apply decompose_not_val in H2; inversion H1; contradiction
        | [ H1 : pot_redex (_ ?e), H2 : decompose ?e _ _ |- _ ] =>
          apply decompose_not_val in H2; inversion H1; contradiction
        | [ H1 : pot_redex (_ ?e _), H2 : decompose ?e _ _ |- _ ] =>
          apply decompose_not_val in H2; inversion H1; contradiction
        | [ H1 : pot_redex (_ _ ?e), H2 : decompose ?e _ _ |- _ ] =>
          apply decompose_not_val in H2; inversion H1; contradiction
        | [ H1 : pot_redex (_ ?e _ _), H2 : decompose ?e _ _ |- _ ] =>
          apply decompose_not_val in H2; inversion H1; contradiction
        | [ H1 : pot_redex (_ _ ?e _), H2 : decompose ?e _ _ |- _ ] =>
          apply decompose_not_val in H2; inversion H1; contradiction
        | [ H1 : pot_redex (_ _ _ ?e), H2 : decompose ?e _ _ |- _ ] =>
          apply decompose_not_val in H2; inversion H1; contradiction
        | [ H1 : val ?e, H2 : decompose ?e _ _ |- _ ] =>
          apply decompose_not_val in H2; contradiction
        | [ D1 : decompose _ ?E1 ?a1, D2 : decompose _ ?E2 ?a2, IHe : forall (E1 E2 : E) (ae1 ae2 : exp), _ 
            |- _ ] => 
          assert (Equal := IHe E1 E2 a1 a2 D1 D2); inversion Equal; subst; auto
      end; subst.
Case "exp_app". rewrite (val_unique p p0); auto.
Case "exp_set". rewrite (val_unique v0 v1); auto.
Case "exp_obj". 
  assert (L := str_exp_list_eq_dec vs vs0).
  destruct L. subst. assert (e0 = e). 

  Check (H3 E0 E2 ae1 ae2 H6 H1).
Qed.
*)
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
Case "redex_getfield".
  destruct (decide_tagof o TagObj).
  inversion H2. destruct (dec_in (fieldnames l) f). 
    exists (plug (lookup_assoc l f exp_err string_eq_dec) E); exists sto0. subst; eapply step_contract... 
    destruct (dec_in (fieldnames l) __proto__).
      exists (plug (exp_getfield (exp_deref (exp_getfield o __proto__)) f) E); exists sto0. subst; eapply step_contract...
      exists (plug exp_undef E); exists sto0. subst; eapply step_contract...
  exists (plug exp_err E); exists sto0; subst; eapply step_contract...
Case "redex_setfield".
  destruct (decide_tagof o TagObj).
  inversion H3. destruct (dec_in (fieldnames l) f).
    exists (plug (exp_obj (update_assoc l f e0 string_eq_dec)) E); exists sto0. subst; eapply step_contract...
    exists (plug (exp_obj ((f,e0)::l)) E); exists sto0. subst; eapply step_contract...
  exists (plug exp_err E); exists sto0; subst; eapply step_contract...
Case "redex_delfield".
  destruct (decide_tagof o TagObj).
  inversion H2. destruct (dec_in (fieldnames l) f). 
    exists (plug (exp_obj (remove_fst f l string_eq_dec)) E); exists sto0.
      subst; eapply step_contract... 
    exists (plug o E); exists sto0. subst; eapply step_contract...
  exists (plug exp_err E); exists sto0; subst; eapply step_contract...
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
  assert (H1 := Coq.Arith.Compare_dec.lt_eq_lt_dec k n).
  destruct H1. destruct s.
  SCase "k < n".
    inversion H. omega.
  SCase "k = n". 
    rewrite <- beq_nat_true_iff in e.
    rewrite -> e.  apply lc_ascend with (k := 0) (k' := k)... omega.
  SCase "k > n". Check beq_nat.
    assert (beq_nat k n = false). rewrite -> beq_nat_false_iff... omega.
    rewrite -> H1...
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
Case "contract_getfield".
  induction l. inversion H1.
  destruct a as (astr, aexp). simpl.
  destruct (string_eq_dec f astr). inversion H0. simpl in H3. inversion H3. apply lc_val...
  apply IHl. inversion H. inversion H4. simpl in *. inversion H7. inversion H9. subst.
  constructor...
  inversion H0. inversion H3. constructor... inversion H4...
  inversion H1. simpl in H2. symmetry in H2; contradiction. auto.
Case "contract_setfield_update".
  induction l. inversion H2.
  destruct a as (astr, aexp). simpl.
  destruct (string_eq_dec f astr). inversion H. subst. inversion H6. simpl in H7. inversion H7. subst.
  constructor... constructor...
  constructor... simpl. 
  unfold fieldnames in *; rewrite <- update_fieldnames_eq. inversion H0. simpl in H5...
  constructor. inversion H; inversion H6; subst. simpl; simpl in H12; inversion H12...
  fold (map (@snd string exp) (update_assoc l f v string_eq_dec)); apply update_values_eq. inversion H0. inversion H4. rewrite Forall_forall in *; subst; intros. apply lc_val... apply lc_val...
Case "contract_setfield_add".
  constructor. simpl. constructor... inversion H0... simpl. constructor... inversion H0...
  rewrite Forall_forall in H4; apply Forall_forall; intros; apply lc_val...
Case "contract_delfield".
  unfold fieldnames in H1; rewrite map_fst_fst_split in H1; apply (in_split_fst f l) in H1. 
  inversion_clear H1; inversion_clear H2; inversion_clear H1. subst.  
  inversion_clear H; inversion_clear H1; subst. unfold fieldnames in H; rewrite map_fst_fst_split in H.  
  rewrite fst_split_comm in H. assert (ND1 := NoDup_remove_1 (fst (split x)) (fst (split x0)) f H).
  assert (ND2 := NoDup_remove_2 (fst (split x)) (fst (split x0)) f H).
  assert (~ (In f (fst (split x)) \/ In f (fst (split x0)))).
  intro. apply (in_or_app (fst (split x)) (fst (split x0)) f) in H1. contradiction. 
  assert (~ In f (fst (split x))). intro; apply H1; left...
  assert (~ In f (fst (split x0))). intro; apply H1; right... clear ND2. clear H1.
  constructor. 
  rewrite remove_app_comm. unfold fieldnames. rewrite map_fst_fst_split. 
  rewrite fst_split_comm2. rewrite fst_split_comm2. simpl. destruct (string_eq_dec f f). simpl.
  rewrite (not_in_remove_eq f x string_eq_dec H3) in ND1. 
  rewrite (not_in_remove_eq f x0 string_eq_dec H4) in ND1...
  rewrite (not_in_remove_eq f x string_eq_dec H3) in H.
  rewrite (not_in_remove_eq f x0 string_eq_dec H4) in H...
  rewrite Forall_forall in H2. rewrite Forall_forall; intros. rewrite remove_app_comm in H1.
  unfold values in H1. rewrite map_snd_snd_split in H1.
  rewrite snd_split_comm2 in H1; rewrite snd_split_comm2 in H1.
  apply in_app_or in H1. inversion_clear H1. apply H2. unfold values. rewrite map_snd_snd_split.
  rewrite snd_split_comm. apply in_or_app. left. rewrite (not_in_remove_eq f x string_eq_dec H3)...
  apply in_app_or in H5. inversion_clear H5. simpl in H1. destruct (string_eq_dec f f). inversion H1. 
  unfold not in n. assert False. apply n... contradiction.
  apply H2. unfold values. rewrite map_snd_snd_split. rewrite snd_split_comm. apply in_or_app. right.
  right. rewrite (not_in_remove_eq f x0 string_eq_dec H4)...
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
