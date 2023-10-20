(** This module contains the definition of the typing relation
  * together with proof of weakening and substitution lemma *)

Require Import Utf8.
Require Import Syntax.

(** Environments.
  * 
  * Since we work with nested-datatypes variable binding representation,
  * type of expressions is parametrized by a set of potentially free variables.
  * These potentially free variables can occur in the expression, so the
  * environment should provide a type for them. Therefore, the type of typing
  * evironments is also parametrized by a set A (of potentially free variables)
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
  * and expressions. *)
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

where "T[ Γ ⊢ e ∷ τ ]" := (@typing _ Γ e τ).

(* ========================================================================= *)

(** Using the classical approach to variable binding, we can use the term t
  * outside the binder as well as under it. This is not true in case of
  * nested-datatype approach: we have to explicitly weaken term (eshift)
  * in order to use it under some binder (see formulation of weakening lemma).
  * Since the weakening is defined in terms of the variable renaming (fmap)
  * we need to generalize the weakeing lemma in order to prove it by
  * induction. *)
Lemma typing_fmap {A B : Set} (f : A → B) (Γ : env A) (Δ : env B) e τ :
  (∀ x, Δ (f x) = Γ x) →
  T[ Γ ⊢ e ∷ τ ] → T[ Δ ⊢ emap f e ∷ τ ].
Proof.
  (* we should generalize on B, f, and Δ in order to get useful induction
   * hypothesis *)
  intros Hf Htyping.
  generalize B f Δ Hf; clear B f Δ Hf.
  induction Htyping; intros B f Δ Hf; simpl.
  + constructor.
  + rewrite <- Hf; constructor.
  + constructor; apply IHHtyping.
    intros [ | x ]; simpl; auto.
  + econstructor; eauto.
Qed.

(** Weakening lemma *)
Lemma typing_weaken {A : Set} (Γ : env A) e τ' τ :
  T[ Γ ⊢ e ∷ τ ] → T[ env_ext Γ τ' ⊢ eshift e ∷ τ ].
Proof.
  apply typing_fmap; reflexivity.
Qed.

(** Since the substitution is defined in terms of the simultaneous
  * substitution (bind), we need to generalize the substitution lemma in order
  * to prove it by induction. *)
Lemma typing_bind {A B : Set} (f : A → value B) (Γ : env A) (Δ : env B) e τ :
  (∀ x, T[ Δ ⊢ f x ∷ Γ x ]) →
  T[ Γ ⊢ e ∷ τ ] → T[ Δ ⊢ ebind f e ∷ τ ].
Proof.
  (* we should generalize on B, f, and Δ in order to get useful induction
   * hypothesis *)
  intros Hf Htyping.
  generalize B f Δ Hf; clear B f Δ Hf.
  induction Htyping; intros B f Δ Hf; simpl.
  + constructor.
  + apply Hf.
  + constructor; apply IHHtyping.
    intros [ | x ]; simpl; [ constructor | ].
    apply typing_weaken with (e := f x).
    apply Hf.
  + econstructor; eauto.
Qed.

(** Substitution lemma *)
Lemma typing_subst {A : Set} (Γ : env A) e (v : value _) τ τ' :
  T[ Γ ⊢ v ∷ τ' ] →
  T[ env_ext Γ τ' ⊢ e ∷ τ ] →
  T[ Γ ⊢ esubst e v ∷ τ ].
Proof.
  intro Hv; apply typing_bind.
  intros [ | x ]; simpl; [ assumption | constructor ].
Qed.