(** This module contains the definition of the typing relation *)

Require Import Utf8.
Require Import Syntax.

(** Environments.
  * 
  * Since we work with nested-datatypes variable binding reprezentation,
  * type of expressions is parametrized by a set A of potentially free variables.
  * These potentially free variables can occur in the expression, so the
  * environment should provide a type for them. Moreover types are parametrized
  * by a set Δ of potentially free type variables. Therefore, the type of typing
  * evironments is parametrized by both types (Δ and A) and is a total function
  * space from A to types. *)
Definition env (Δ A : Set) : Set := A → type Δ.

(** Empty environment *)
Definition env_empty : env Empty_set Empty_set :=
  λ x, match x with end.

(** Extending the environment *)
Definition env_ext {Δ A : Set} (Γ : env Δ A) (τ : type Δ) : env Δ (inc A) :=
  λ x,
  match x with
  | VZ   => τ
  | VS y => Γ y
  end.

(** Shifting the environment, i.e., extending by a fresh type variable. *)
Definition env_shift {Δ A : Set} (Γ : env Δ A) : env (inc Δ) A :=
  λ x, tshift (Γ x).

(* We introduce some human-readable notation for typing. Because Δ follows
 * directly from a type of Γ, we make this environment implicit. *)
Reserved Notation "'T[' Γ '⊢' e '∷' τ ']'".

(** The typing relation.
  *
  * The "set of potentially free variables" must agree between environments
  * and expressions. Environment Δ is implicit – it follows from the type
  * of Γ. *)
Inductive typing {Δ A : Set} (Γ : env Δ A) : expr A → type Δ → Prop :=
| T_Var : ∀ x,
    T[ Γ ⊢ v_var x ∷ Γ x ]

| T_Lam : ∀ e τ₁ τ₂,
    T[ env_ext Γ τ₁ ⊢ e ∷ τ₂ ] →
    (*----------------------------*)
    T[ Γ ⊢ v_lam e ∷ t_arrow τ₁ τ₂ ]

| T_TLam : ∀ e τ,
    T[ env_shift Γ ⊢ e ∷ τ ] →
    (*--------------------------*)
    T[ Γ ⊢ v_tlam e ∷ t_forall τ ]

| T_App : ∀ e₁ e₂ τ₂ τ₁,
    T[ Γ ⊢ e₁ ∷ t_arrow τ₂ τ₁ ] →
    T[ Γ ⊢ e₂ ∷ τ₂ ] →
    (*-------------------------*)
    T[ Γ ⊢ e_app e₁ e₂ ∷ τ₁ ]

| T_TApp : ∀ e τ τ',
    T[ Γ ⊢ e ∷ t_forall τ ] →
    (*---------------------------*)
    T[ Γ ⊢ e_tapp e ∷ tsubst τ τ' ]

where "T[ Γ ⊢ e ∷ τ ]" := (@typing _ _ Γ e τ).