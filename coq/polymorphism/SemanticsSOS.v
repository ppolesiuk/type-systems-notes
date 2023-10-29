(** This module provides the SOS semantics *)

Require Import Utf8.
Require Import Syntax.
Require Import Relation_Operators.

(** SOS reduction rules *)
Inductive red {A : Set} : expr A → expr A → Prop :=
| red_beta : ∀ e (v : value A),
    red (e_app (v_lam e) v) (esubst e v)

| red_tbeta : ∀ e,
    red (e_tapp (v_tlam e)) e

| red_app1 : ∀ e₁ e₁' e₂,
    red e₁ e₁' →
    red (e_app e₁ e₂) (e_app e₁' e₂)

| red_app2 : ∀ (v : value A) e e',
    red e e' →
    red (e_app v e) (e_app v e')

| red_tapp : ∀ e e',
    red e e' →
    red (e_tapp e) (e_tapp e')
.

(** Reflexive and transitive closure of a reduction relation *)
Notation red_rtc e₁ e₂ := (clos_refl_trans_1n _ red e₁ e₂).

(** We use SOS, but inside-out evaluation contexts are still useful in
 * defining biorthogonal closure. The following lemma connects evaluation
 * contexts with SOS. *)
Lemma red_in_ectx {A : Set} (E : ectx A) (e e' : expr A) :
  red e e' → red (plug E e) (plug E e').
Proof.
  generalize e e'; clear e e'; induction E; intros; simpl;
    assumption || apply IHE;
    [ apply red_app1 | apply red_app2 | apply red_tapp ];
    assumption.
Qed.