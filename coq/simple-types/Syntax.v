(** This module contains the definition of syntax, together with basic
 * syntactic operations like substitution or variable renaming. *)

Require Import Utf8.

(** Adding one element to a type *)
Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.

Arguments VZ {V}.
Arguments VS {V}.

(** Types *)
Inductive type : Set :=
| t_unit  : type
| t_arrow : type → type → type
.

(** Expressions and values *)
Inductive expr (V : Set) : Set :=
| e_value : value V → expr V
| e_app   : expr V → expr V → expr V

with value (V : Set) : Set :=
| v_var  : V → value V
| v_lam  : expr (inc V) → value V
| v_unit : value V
.

Arguments e_value {V}.
Arguments e_app   {V}.

Arguments v_var   {V}.
Arguments v_lam   {V}.
Arguments v_unit  {V}.

(* We register e_value as coercion in order to allow values in any context
 * where expressions are expected. *)
Coercion e_value : value >-> expr.

(* ========================================================================= *)
(* Mapping, i.e., variable renaming *)

(** Lifting of renamings (↑ operation) *)
Definition liftA {A B : Set} (f : A → B) (x : inc A) : inc B :=
  match x with
  | VZ   => VZ
  | VS y => VS (f y)
  end.

(** Mapping of expressions and values († operation) *)
Fixpoint emap {A B : Set} (f : A → B) (e : expr A) : expr B :=
  match e with
  | e_value   v => vmap f v
  | e_app e₁ e₂ => e_app (emap f e₁) (emap f e₂)
  end
with vmap {A B : Set} (f : A → B) (v : value A) : value B :=
  match v with
  | v_var x => v_var (f x)
  | v_lam e => v_lam (emap (liftA f) e)
  | v_unit  => v_unit
  end.

(** Shifting of expressions (s† operation). This operation shifts expression
  * to a context where one more variable is allowed *)
Definition eshift {A : Set} (e : expr A) : expr (inc A) := emap VS e.

(** Shifting of values *)
Definition vshift {A : Set} (v : value A) : value (inc A) := vmap VS v.

(* ========================================================================= *)
(* Binding, i.e., simultaneous substitution *)

(** Lifting of substitution (⇑ operation) *)
Definition liftS {A B : Set} (f : A → value B) (x : inc A) : value (inc B) :=
  match x with
  | VZ   => v_var VZ
  | VS y => vshift (f y)
  end.

(** Binding of expressions and value ( * operation) *)
Fixpoint ebind {A B : Set} (f : A → value B) (e : expr A) : expr B :=
  match e with
  | e_value   v => vbind f v
  | e_app e₁ e₂ => e_app (ebind f e₁) (ebind f e₂)
  end
with vbind {A B : Set} (f : A → value B) (v : value A) : value B :=
  match v with
  | v_var x => f x
  | v_lam e => v_lam (ebind (liftS f) e)
  | v_unit  => v_unit
  end.

(** Extending substitution (◃ operation) *)
Definition scons {A B : Set} (v : value B) (f : A → value B) (x : inc A) :
    value B :=
  match x with
  | VZ   => v
  | VS y => f y
  end.

(** Substitution of single value in expression *)
Definition esubst {A : Set} (e : expr (inc A)) (v : value A) : expr A :=
  ebind (scons v v_var) e.

(** Substitution of single value in value *)
Definition vsubst {A : Set} (v' : value (inc A)) (v : value A) : value A :=
  vbind (scons v v_var) v'.