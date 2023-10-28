(** This module contains the definition of the typing relation. *)

Require Import Utf8.
Require Import Syntax.

(** Environments.
  * 
  * Since we work with nested-datatypes variable binding representation,
  * type of expressions is parametrized by a set of potentially free variables.
  * These potentially free variables can occur in the expression, so the
  * environment should provide a type for them. Therefore, the type of typing
  * environments is also parametrized by a set A (of potentially free variables)
  * and is a total function space from A to types. *)
Definition env (A : Set) : Set := A → type.

(** Empty environment *)
Definition env_empty : env Empty_set :=
  λ x, match x with end.

(** Extending the environment *)
Definition env_ext {A : Set} (Γ : env A) (τ : type) : env (inc A) :=
  λ x,
  match x with
  | VZ   => τ
  | VS y => Γ y
  end.

(* We introduce some human-readable notation for typing *)
Reserved Notation "'T[' Γ '⊢' e '∷' τ ']'".

(** The typing relation.
  *
  * The "set of potentially free variables" must agree between environments
  * and expressions.
  *
  * There are two design decisions that require additional comments.
  * - There is no typing rule for abort, as we see it as a runtime construct.
  *   Programmer should not be able to write an abort in his program.
  * - The ⊥-elimination (T_Absurd rule) is not syntax directed. Alternative
  *   approach would be to introduce absurd construct in the grammar of
  *   expressions. Our approach is more convenient for the programmer, but
  *   requires non syntax directed rules, that introduces some minor problems,
  *   when we want to prove properties via progress+preservation. Since we use
  *   logical relations in this example, this approach seems to be more
  *   convenient. *)
Inductive typing {A : Set} (Γ : env A) : expr A → type → Prop :=
| T_Unit :
    T[ Γ ⊢ v_unit ∷ t_unit ]

| T_Var : ∀ x,
    T[ Γ ⊢ v_var x ∷ Γ x ]

| T_Lam : ∀ e τ₁ τ₂,
    T[ env_ext Γ τ₁ ⊢ e ∷ τ₂ ] →
    (*----------------------------*)
    T[ Γ ⊢ v_lam e ∷ t_arrow τ₁ τ₂ ]

| T_App : ∀ e₁ e₂ τ₂ τ₁,
    T[ Γ ⊢ e₁ ∷ t_arrow τ₂ τ₁ ] →
    T[ Γ ⊢ e₂ ∷ τ₂ ] →
    (*----------------------------*)
    T[ Γ ⊢ e_app e₁ e₂ ∷ τ₁ ]

| T_CallCC : ∀ e τ,
    T[ env_ext Γ (t_arrow τ t_bot) ⊢ e ∷ τ ] →
    (*---------------------------------------*)
    T[ Γ ⊢ e_callcc e ∷ τ ]

| T_Absurd : ∀ e τ,
    T[ Γ ⊢ e ∷ t_bot ] →
    (*----------------*)
    T[ Γ ⊢ e ∷ τ ]

where "T[ Γ ⊢ e ∷ τ ]" := (@typing _ Γ e τ).