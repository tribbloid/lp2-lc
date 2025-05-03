/-
 * Preservation and Progress for System-F with Subtyping - Definitions
 * Converted from Coq to Lean 4
 * Original by Brian Aydemir & Arthur Charguéraud, March 2007
 -/

import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation

-- We'll need to define our own library functions to match LibLN in the Coq code
namespace LibLN

/-- Represents a set of variables -/
def vars := Finset String

/-- Empty set of variables -/
def empty_vars : vars := ∅

/-- Singleton set containing one variable -/
def singleton_var (x : String) : vars := {x}

/-- Union of two variable sets -/
def union_vars (s1 s2 : vars) : vars := s1 ∪ s2

/-- Check if a variable is in a set -/
def var_in (x : String) (s : vars) : Prop := x ∈ s

/-- Check if a variable is not in a set -/
def var_notin (x : String) (s : vars) : Prop := x ∉ s

/-- Fresh variable: x is not in L -/
def fresh (x : String) (L : vars) : Prop := var_notin x L

/-- Environment as an association list -/
def env (A : Type) := List (String × A)

/-- Empty environment -/
def empty_env {A : Type} : env A := []

/-- Check if a key is bound in an environment -/
def binds {A : Type} (x : String) (v : A) (E : env A) : Prop :=
  (x, v) ∈ E

/-- Check if a key is fresh in an environment -/
def fresh_in_env {A : Type} (x : String) (E : env A) : Prop :=
  ¬ ∃ v, binds x v E

/-- Notation for fresh_in_env -/
notation:50 x " # " E => fresh_in_env x E

/-- Concatenate two environments -/
def concat_env {A : Type} (E F : env A) : env A := F ++ E

/-- Add a binding to an environment -/
def push_env {A : Type} (x : String) (v : A) (E : env A) : env A := 
  concat_env E [(x, v)]

/-- Notation for environment concatenation -/
notation:60 E " & " F => concat_env E F

/-- Notation for pushing a binding -/
notation:60 E " & " x " ~ " v => push_env x v E

/-- Map a function over an environment -/
def map_env {A B : Type} (f : A → B) (E : env A) : env B :=
  E.map (fun (x, v) => (x, f v))

end LibLN

-- Main definitions for System F with subtyping
open LibLN

-- Type variables and term variables are represented as strings
def var := String

-- Implicit type declarations
variable (x y z : var)
variable (X Y Z : var)

/-- Representation of pre-types -/
inductive typ : Type
  | typ_top : typ
  | typ_bvar : Nat → typ
  | typ_fvar : var → typ
  | typ_arrow : typ → typ → typ
  | typ_all : typ → typ → typ

/-- Representation of pre-terms -/
inductive trm : Type
  | trm_bvar : Nat → trm
  | trm_fvar : var → trm
  | trm_abs : typ → trm → trm
  | trm_app : trm → trm → trm
  | trm_tabs : typ → trm → trm
  | trm_tapp : trm → typ → trm

open typ
open trm

/-- Opening up a type binder occurring in a type -/
def open_tt_rec (k : Nat) (u : typ) : typ → typ
  | typ_top => typ_top
  | typ_bvar j => if k = j then u else typ_bvar j
  | typ_fvar x => typ_fvar x
  | typ_arrow t1 t2 => typ_arrow (open_tt_rec k u t1) (open_tt_rec k u t2)
  | typ_all t1 t2 => typ_all (open_tt_rec k u t1) (open_tt_rec (k+1) u t2)

/-- Opening with index 0 -/
def open_tt (t : typ) (u : typ) : typ := open_tt_rec 0 u t

/-- Opening up a type binder occurring in a term -/
def open_te_rec (k : Nat) (u : typ) : trm → trm
  | trm_bvar i => trm_bvar i
  | trm_fvar x => trm_fvar x
  | trm_abs v e1 => trm_abs (open_tt_rec k u v) (open_te_rec k u e1)
  | trm_app e1 e2 => trm_app (open_te_rec k u e1) (open_te_rec k u e2)
  | trm_tabs v e1 => trm_tabs (open_tt_rec k u v) (open_te_rec (k+1) u e1)
  | trm_tapp e1 v => trm_tapp (open_te_rec k u e1) (open_tt_rec k u v)

/-- Opening with index 0 -/
def open_te (t : trm) (u : typ) : trm := open_te_rec 0 u t

/-- Opening up a term binder occurring in a term -/
def open_ee_rec (k : Nat) (f : trm) : trm → trm
  | trm_bvar i => if k = i then f else trm_bvar i
  | trm_fvar x => trm_fvar x
  | trm_abs v e1 => trm_abs v (open_ee_rec (k+1) f e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm_tabs v e1 => trm_tabs v (open_ee_rec k f e1)
  | trm_tapp e1 v => trm_tapp (open_ee_rec k f e1) v

/-- Opening with index 0 -/
def open_ee (t : trm) (u : trm) : trm := open_ee_rec 0 u t

/-- Notation for opening up binders with type or term variables -/
def open_tt_var (t : typ) (x : var) : typ := open_tt t (typ_fvar x)
def open_te_var (t : trm) (x : var) : trm := open_te t (typ_fvar x)
def open_ee_var (t : trm) (x : var) : trm := open_ee t (trm_fvar x)

/-- Types as locally closed pre-types -/
inductive type : typ → Prop
  | type_top : type typ_top
  | type_var : ∀ (X : var), type (typ_fvar X)
  | type_arrow : ∀ (T1 T2 : typ), 
      type T1 → 
      type T2 → 
      type (typ_arrow T1 T2)
  | type_all : ∀ (L : vars) (T1 T2 : typ),
      type T1 →
      (∀ (X : var), var_notin X L → type (open_tt_var T2 X)) →
      type (typ_all T1 T2)

/-- Terms as locally closed pre-terms -/
inductive term : trm → Prop
  | term_var : ∀ (x : var),
      term (trm_fvar x)
  | term_abs : ∀ (L : vars) (V : typ) (e1 : trm),
      type V →
      (∀ (x : var), var_notin x L → term (open_ee_var e1 x)) →
      term (trm_abs V e1)
  | term_app : ∀ (e1 e2 : trm),
      term e1 →
      term e2 →
      term (trm_app e1 e2)
  | term_tabs : ∀ (L : vars) (V : typ) (e1 : trm),
      type V →
      (∀ (X : var), var_notin X L → term (open_te_var e1 X)) →
      term (trm_tabs V e1)
  | term_tapp : ∀ (e1 : trm) (V : typ),
      term e1 →
      type V →
      term (trm_tapp e1 V)

/-- Bindings are either mapping type or term variables -/
inductive bind : Type
  | bind_sub : typ → bind
  | bind_typ : typ → bind

open bind

/-- Environment is an associative list of bindings -/
def env := LibLN.env bind

/-- Notations for bindings -/
notation:60 X " ~<: " T => (X, bind_sub T)
notation:60 x " ~: " T => (x, bind_typ T)

/-- Well-formedness of a pre-type T in an environment E -/
inductive wft : env → typ → Prop
  | wft_top : ∀ (E : env),
      wft E typ_top
  | wft_var : ∀ (U : typ) (E : env) (X : var),
      binds X (bind_sub U) E →
      wft E (typ_fvar X)
  | wft_arrow : ∀ (E : env) (T1 T2 : typ),
      wft E T1 →
      wft E T2 →
      wft E (typ_arrow T1 T2)
  | wft_all : ∀ (L : vars) (E : env) (T1 T2 : typ),
      wft E T1 →
      (∀ (X : var), var_notin X L →
        wft (E & X ~<: T1) (open_tt_var T2 X)) →
      wft E (typ_all T1 T2)

/-- A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to -/
inductive okt : env → Prop
  | okt_empty :
      okt empty_env
  | okt_sub : ∀ (E : env) (X : var) (T : typ),
      okt E → wft E T → X # E → okt (E & X ~<: T)
  | okt_typ : ∀ (E : env) (x : var) (T : typ),
      okt E → wft E T → x # E → okt (E & x ~: T)

/-- Subtyping relation -/
inductive sub : env → typ → typ → Prop
  | sub_top : ∀ (E : env) (S : typ),
      okt E →
      wft E S →
      sub E S typ_top
  | sub_refl_tvar : ∀ (E : env) (X : var),
      okt E →
      wft E (typ_fvar X) →
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : ∀ (U : typ) (E : env) (T : typ) (X : var),
      binds X (bind_sub U) E →
      sub E U T →
      sub E (typ_fvar X) T
  | sub_arrow : ∀ (E : env) (S1 S2 T1 T2 : typ),
      sub E T1 S1 →
      sub E S2 T2 →
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : ∀ (L : vars) (E : env) (S1 S2 T1 T2 : typ),
      sub E T1 S1 →
      (∀ (X : var), var_notin X L →
          sub (E & X ~<: T1) (open_tt_var S2 X) (open_tt_var T2 X)) →
      sub E (typ_all S1 S2) (typ_all T1 T2)

/-- Typing relation -/
inductive typing : env → trm → typ → Prop
  | typing_var : ∀ (E : env) (x : var) (T : typ),
      okt E →
      binds x (bind_typ T) E →
      typing E (trm_fvar x) T
  | typing_abs : ∀ (L : vars) (E : env) (V : typ) (e1 : trm) (T1 : typ),
      (∀ (x : var), var_notin x L →
        typing (E & x ~: V) (open_ee_var e1 x) T1) →
      typing E (trm_abs V e1) (typ_arrow V T1)
  | typing_app : ∀ (T1 : typ) (E : env) (e1 e2 : trm) (T2 : typ),
      typing E e1 (typ_arrow T1 T2) →
      typing E e2 T1 →
      typing E (trm_app e1 e2) T2
  | typing_tabs : ∀ (L : vars) (E : env) (V : typ) (e1 : trm) (T1 : typ),
      (∀ (X : var), var_notin X L →
        typing (E & X ~<: V) (open_te_var e1 X) (open_tt_var T1 X)) →
      typing E (trm_tabs V e1) (typ_all V T1)
  | typing_tapp : ∀ (T1 : typ) (E : env) (e1 : trm) (T : typ) (T2 : typ),
      typing E e1 (typ_all T1 T2) →
      sub E T T1 →
      typing E (trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : ∀ (S : typ) (E : env) (e : trm) (T : typ),
      typing E e S →
      sub E S T →
      typing E e T

/-- Values -/
inductive value : trm → Prop
  | value_abs : ∀ (V : typ) (e1 : trm), 
      term (trm_abs V e1) →
      value (trm_abs V e1)
  | value_tabs : ∀ (V : typ) (e1 : trm), 
      term (trm_tabs V e1) →
      value (trm_tabs V e1)

/-- One-step reduction -/
inductive red : trm → trm → Prop
  | red_app_1 : ∀ (e1 e1' e2 : trm),
      term e2 →
      red e1 e1' →
      red (trm_app e1 e2) (trm_app e1' e2)
  | red_app_2 : ∀ (e1 e2 e2' : trm),
      value e1 →
      red e2 e2' →
      red (trm_app e1 e2) (trm_app e1 e2')
  | red_tapp : ∀ (e1 e1' : trm) (V : typ),
      type V →
      red e1 e1' →
      red (trm_tapp e1 V) (trm_tapp e1' V)
  | red_abs : ∀ (V : typ) (e1 v2 : trm),
      term (trm_abs V e1) →
      value v2 →
      red (trm_app (trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : ∀ (V1 : typ) (e1 : trm) (V2 : typ),
      term (trm_tabs V1 e1) →
      type V2 →
      red (trm_tapp (trm_tabs V1 e1) V2) (open_te e1 V2)

/-- Our goal is to prove preservation and progress -/
def preservation := ∀ (E : env) (e e' : trm) (T : typ),
  typing E e T →
  red e e' →
  typing E e' T

def progress := ∀ (e : trm) (T : typ),
  typing empty_env e T →
  value e ∨ ∃ (e' : trm), red e e'

/-- Computing free type variables in a type -/
def fv_tt : typ → vars
  | typ_top => empty_vars
  | typ_bvar _ => empty_vars
  | typ_fvar X => singleton_var X
  | typ_arrow T1 T2 => union_vars (fv_tt T1) (fv_tt T2)
  | typ_all T1 T2 => union_vars (fv_tt T1) (fv_tt T2)

/-- Computing free type variables in a term -/
def fv_te : trm → vars
  | trm_bvar _ => empty_vars
  | trm_fvar _ => empty_vars
  | trm_abs V e1 => union_vars (fv_tt V) (fv_te e1)
  | trm_app e1 e2 => union_vars (fv_te e1) (fv_te e2)
  | trm_tabs V e1 => union_vars (fv_tt V) (fv_te e1)
  | trm_tapp e1 V => union_vars (fv_te e1) (fv_tt V)

/-- Computing free term variables in a term -/
def fv_ee : trm → vars
  | trm_bvar _ => empty_vars
  | trm_fvar x => singleton_var x
  | trm_abs _ e1 => fv_ee e1
  | trm_app e1 e2 => union_vars (fv_ee e1) (fv_ee e2)
  | trm_tabs _ e1 => fv_ee e1
  | trm_tapp e1 _ => fv_ee e1

/-- Substitution for free type variables in types -/
def subst_tt (Z : var) (U : typ) : typ → typ
  | typ_top => typ_top
  | typ_bvar j => typ_bvar j
  | typ_fvar X => if X = Z then U else typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T1 T2 => typ_all (subst_tt Z U T1) (subst_tt Z U T2)

/-- Substitution for free type variables in terms -/
def subst_te (Z : var) (U : typ) : trm → trm
  | trm_bvar i => trm_bvar i
  | trm_fvar x => trm_fvar x
  | trm_abs V e1 => trm_abs (subst_tt Z U V) (subst_te Z U e1)
  | trm_app e1 e2 => trm_app (subst_te Z U e1) (subst_te Z U e2)
  | trm_tabs V e1 => trm_tabs (subst_tt Z U V) (subst_te Z U e1)
  | trm_tapp e1 V => trm_tapp (subst_te Z U e1) (subst_tt Z U V)

/-- Substitution for free term variables in terms -/
def subst_ee (z : var) (u : trm) : trm → trm
  | trm_bvar i => trm_bvar i
  | trm_fvar x => if x = z then u else trm_fvar x
  | trm_abs V e1 => trm_abs V (subst_ee z u e1)
  | trm_app e1 e2 => trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm_tabs V e1 => trm_tabs V (subst_ee z u e1)
  | trm_tapp e1 V => trm_tapp (subst_ee z u e1) V

/-- Substitution for free type variables in environment -/
def subst_tb (Z : var) (P : typ) : bind → bind
  | bind_sub T => bind_sub (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tt Z P T)

/-- Theorems and proofs would follow here -/
-- The proofs would be quite extensive, similar to the original Coq file
-- For brevity, we're omitting the proofs in this translation
