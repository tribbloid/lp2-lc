import Mathlib.Logic.Basic
import Mathlib.Data.Finset.Basic

-- Define variables
variable (var : Type)

-- Define types
inductive typ : Type
| top : typ
| bvar : Nat → typ
| fvar : var → typ
| arrow : typ → typ → typ
| all : typ → typ → typ

-- Define terms
inductive trm : Type
| bvar : Nat → trm
| fvar : var → trm
| abs : typ → trm → trm
| app : trm → trm → trm
| tabs : typ → trm → trm
| tapp : trm → typ → trm

-- Define opening for types
def open_tt_rec : Nat → typ → typ → typ
| _, _, typ.top => typ.top
| k, u, typ.bvar i => if k = i then u else typ.bvar i
| _, _, typ.fvar x => typ.fvar x
| k, u, typ.arrow t1 t2 => typ.arrow (open_tt_rec k u t1) (open_tt_rec k u t2)
| k, u, typ.all t1 t2 => typ.all (open_tt_rec k u t1) (open_tt_rec (k+1) u t2)

def open_tt (t u : typ) : typ := open_tt_rec 0 u t

-- Define opening for terms
def open_te_rec : Nat → typ → trm → trm
| _, _, trm.bvar i => trm.bvar i
| _, _, trm.fvar x => trm.fvar x
| k, u, trm.abs v e => trm.abs (open_tt_rec k u v) (open_te_rec k u e)
| k, u, trm.app e1 e2 => trm.app (open_te_rec k u e1) (open_te_rec k u e2)
| k, u, trm.tabs v e => trm.tabs (open_tt_rec k u v) (open_te_rec (k+1) u e)
| k, u, trm.tapp e v => trm.tapp (open_te_rec k u e) (open_tt_rec k u v)

def open_te (t : trm) (u : typ) : trm := open_te_rec 0 u t

-- Define locally closed types
inductive type : typ → Prop
| top : type typ.top
| var : ∀ x, type (typ.fvar x)
| arrow : ∀ t1 t2, type t1 → type t2 → type (typ.arrow t1 t2)
| all : ∀ t1 t2, type t1 → (∀ x, x ∉ fv_tt t2 → type (open_tt t2 (typ.fvar x))) → type (typ.all t1 t2)

-- Define locally closed terms
inductive term : trm → Prop
| var : ∀ x, term (trm.fvar x)
| abs : ∀ v e, type v → (∀ x, x ∉ fv_ee e → term (open_ee e (trm.fvar x))) → term (trm.abs v e)
| app : ∀ e1 e2, term e1 → term e2 → term (trm.app e1 e2)
| tabs : ∀ v e, type v → (∀ x, x ∉ fv_te e → term (open_te e (typ.fvar x))) → term (trm.tabs v e)
| tapp : ∀ e v, term e → type v → term (trm.tapp e v)

-- Define bindings
inductive bind : Type
| sub : typ → bind
| typ : typ → bind

-- Define environment
def env := List (var × bind)

-- Define well-formedness of types in an environment
inductive wft : env → typ → Prop
| top : ∀ e, wft e typ.top
| var : ∀ e x u, (x, bind.sub u) ∈ e → wft e (typ.fvar x)
| arrow : ∀ e t1 t2, wft e t1 → wft e t2 → wft e (typ.arrow t1 t2)
| all : ∀ e t1 t2, wft e t1 → (∀ x, x ∉ dom e → wft ((x, bind.sub t1) :: e) (open_tt t2 (typ.fvar x))) → wft e (typ.all t1 t2)

-- Define well-formedness of environments
inductive okt : env → Prop
| empty : okt []
| sub : ∀ e x t, okt e → wft e t → x ∉ dom e → okt ((x, bind.sub t) :: e)
| typ : ∀ e x t, okt e → wft e t → x ∉ dom e → okt ((x, bind.typ t) :: e)

-- Define subtyping relation
inductive sub : env → typ → typ → Prop
| top : ∀ e s, okt e → wft e s → sub e s typ.top
| refl_tvar : ∀ e x, okt e → wft e (typ.fvar x) → sub e (typ.fvar x) (typ.fvar x)
| trans_tvar : ∀ e x u t, (x, bind.sub u) ∈ e → sub e u t → sub e (typ.fvar x) t
| arrow : ∀ e s1 s2 t1 t2, sub e t1 s1 → sub e s2 t2 → sub e (typ.arrow s1 s2) (typ.arrow t1 t2)
| all : ∀ e s1 s2 t1 t2, sub e t1 s1 → (∀ x, x ∉ dom e → sub ((x, bind.sub t1) :: e) (open_tt s2 (typ.fvar x)) (open_tt t2 (typ.fvar x))) → sub e (typ.all s1 s2) (typ.all t1 t2)

-- Define typing relation
inductive typing : env → trm → typ → Prop
| var : ∀ e x t, okt e → (x, bind.typ t) ∈ e → typing e (trm.fvar x) t
| abs : ∀ e v e1 t1, (∀ x, x ∉ dom e → typing ((x, bind.typ v) :: e) (open_ee e1 (trm.fvar x)) t1) → typing e (trm.abs v e1) (typ.arrow v t1)
| app : ∀ e e1 e2 t1 t2, typing e e1 (typ.arrow t1 t2) → typing e e2 t1 → typing e (trm.app e1 e2) t2
| tabs : ∀ e v e1 t1, (∀ x, x ∉ dom e → typing ((x, bind.sub v) :: e) (open_te e1 (typ.fvar x)) (open_tt t1 (typ.fvar x))) → typing e (trm.tabs v e1) (typ.all v t1)
| tapp : ∀ e e1 t t1 t2, typing e e1 (typ.all t1 t2) → sub e t t1 → typing e (trm.tapp e1 t) (open_tt t2 t)
| sub : ∀ e e s t, typing e e s → sub e s t → typing e e t

-- Define values
inductive value : trm → Prop
| abs : ∀ v e, term (trm.abs v e) → value (trm.abs v e)
| tabs : ∀ v e, term (trm.tabs v e) → value (trm.tabs v e)

-- Define reduction relation
inductive red : trm → trm → Prop
| app_1 : ∀ e1 e1' e2, term e2 → red e1 e1' → red (trm.app e1 e2) (trm.app e1' e2)
| app_2 : ∀ e1 e2 e2', value e1 → red e2 e2' → red (trm.app e1 e2) (trm.app e1 e2')
| tapp : ∀ e1 e1' v, type v → red e1 e1' → red (trm.tapp e1 v) (trm.tapp e1' v)
| abs : ∀ v e1 v2, term (trm.abs v e1) → value v2 → red (trm.app (trm.abs v e1) v2) (open_ee e1 v2)
| tabs : ∀ v1 e1 v2, term (trm.tabs v1 e1) → type v2 → red (trm.tapp (trm.tabs v1 e1) v2) (open_te e1 v2)

-- Define preservation and progress
def preservation := ∀ e t t' T, typing e t T → red t t' → typing e t' T

def progress := ∀ t T, typing [] t T → value t ∨ ∃ t', red t t'

-- Start of proofs
theorem sub_reflexivity : ∀ e t, okt e → wft e t → sub e t t := sorry

theorem sub_weakening : ∀ e f g s t,
  sub (e ++ g) s t → okt (e ++ f ++ g) → sub (e ++ f ++ g) s t := sorry

-- Continue with other lemmas and theorems...

theorem preservation_result : preservation := sorry

theorem progress_result : progress := sorry
