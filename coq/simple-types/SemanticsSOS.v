(** This module provides the SOS semantics *)

Require Import Utf8.
Require Import Syntax.
Require Import Relation_Operators.

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

(** Reflexive and transitive closure of a reduction relation *)
Notation red_rtc e₁ e₂ := (clos_refl_trans_1n _ red e₁ e₂).

Inductive is_value {A : Set} : expr A → Prop :=
| is_val : ∀ v : value _, is_value v
.

Lemma is_value_dec {A : Set} (e : expr A) :
  {is_value e} + {¬is_value e}.
Proof.
  destruct e;
    (left; constructor; fail) ||
    (right; intro H; inversion H).
Qed.

(** Safety property *)
Definition safe {A : Set} (e : expr A) : Prop :=
  ∀ e', red_rtc e e' → is_value e' ∨ ∃ e'', red e' e''.

(** Reduction is deterministic *)
Lemma red_deterministic {A : Set} {e e₁ e₂ : expr A} :
  red e e₁ → red e e₂ → e₁ = e₂.
Proof.
  intro Hred; generalize e₂; clear e₂.
  induction Hred; intros ? Hred2; inversion Hred2; subst; clear Hred2;
    repeat match goal with
    | [ |- ?e = ?e ] => reflexivity
    | [ H: red (e_value _) _ |- _ ] => inversion H (* values do not reduce *)
    | [ IH: ∀ _, red _ _ → _ = _ |- _ ] =>
      erewrite IH; [ reflexivity | ]; assumption
    end.
Qed.

Lemma red_rtc_app1 {A : Set} (e₁ e₁' e₂ : expr A) :
  red_rtc e₁ e₁' →
  red_rtc (e_app e₁ e₂) (e_app e₁' e₂).
Proof.
  induction 1; econstructor; [ apply red_app1 | ]; eassumption.
Qed.

Lemma value_red_rtc_to_value {A : Set} (v : value A) e :
  red_rtc v e → is_value e.
Proof.
  inversion 1; [ constructor | ].
  match goal with
  | [ H: red (e_value _) _ |- _ ] => inversion H
  end.
Qed.

(* ========================================================================= *)
(* Inversion of reflexive-transitive closure of reduction for application.
 * During the lecture, we said that the main lemma of this section
 * `red_rtc_app_inv` is obvious. In Coq we have to prove it, and it requires
 * some work. These lemma is important only in the SafetyLogicalRealtion. *)

Inductive red_rtc_app_inv_class {A : Set} (e₁ e₂ : expr A) : expr A → Prop :=
| rrapp_inv1 : ∀ e₁',
    red_rtc e₁ e₁' →
    ¬ is_value e₁' →
    red_rtc_app_inv_class e₁ e₂ (e_app e₁' e₂)
| rrapp_inv2 : ∀ (v₁ : value A) e₂',
    red_rtc e₁ v₁ →
    red_rtc e₂ e₂' →
    ¬ is_value e₂' →
    red_rtc_app_inv_class e₁ e₂ (e_app v₁ e₂')
| rrapp_inv3 : ∀ (v₁ v₂ : value A) e,
    red_rtc e₁ v₁ →
    red_rtc e₂ v₂ →
    red_rtc (e_app v₁ v₂) e →
    red_rtc_app_inv_class e₁ e₂ e
.

Lemma red_rtc_app_inv {A : Set} {e₁ e₂ e : expr A} :
  red_rtc (e_app e₁ e₂) e → red_rtc_app_inv_class e₁ e₂ e.
Proof.
  intro Hred; remember (e_app e₁ e₂) as e₀.
  generalize e₁ e₂ Heqe₀; clear e₁ e₂ Heqe₀.
  induction Hred as [ | e e' e'' Hred Hrtc IH ].
  + intros e₁ e₂ Heq; subst.
    destruct (is_value_dec e₁) as [ [ v₁ ] | ].
    - destruct (is_value_dec e₂) as [ [ v₂ ] | ].
      * eapply rrapp_inv3; constructor.
      * apply rrapp_inv2; try assumption; constructor.
    - apply rrapp_inv1; [ constructor | assumption ].
  + intros e₁ e₂ Heq; subst.
    inversion Hred; clear Hred; subst.
    - eapply rrapp_inv3; [ constructor | constructor | ].
      econstructor; [ apply red_beta | eassumption ].
    - specialize (IH _ _ eq_refl); destruct IH.
      * apply rrapp_inv1; [ | assumption ].
        econstructor; eassumption.
      * apply rrapp_inv2; try assumption; [].
        econstructor; eassumption.
      * eapply rrapp_inv3; try eassumption; [].
        econstructor; eassumption.
    - specialize (IH _ _ eq_refl); destruct IH as [ ? ? Hval | | ].
      * exfalso; apply Hval.
        eapply value_red_rtc_to_value; eassumption.
      * apply rrapp_inv2; try assumption; [].
        econstructor; eassumption.
      * eapply rrapp_inv3; try eassumption; [].
        econstructor; eassumption.
Qed.