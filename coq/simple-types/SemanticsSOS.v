(** This module provides the SOS semantics *)

Require Import Utf8.
Require Import Syntax.

(** SOS reduction rules *)
Inductive red {A : Set} : expr A → expr A → Prop :=
| red_beta : ∀ e (v : value A),
    red (e_app (v_lam e) v) (esubst e v)

| red_app1 : ∀ e₁ e₁' e₂,
    red e₁ e₁' →
    red (e_app e₁ e₂) (e_app e₁' e₂)

| red_app2 : ∀ (v : value A) e e',
    red e e' →
    red (e_app v e) (e_app v e')
.