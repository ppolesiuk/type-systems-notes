(** Here, we prove a termination property using logical relations.
  * For pedagogcal reasons, most of the code is copy-pased from
  * SafetyLogicalRelation module. Developing more reusable code would only
  * obscure the presentation. *)

Require Import Utf8.
Require Import Syntax SemanticsSOS Typing.

(** Semantic types: unary relations on closed values *)
Definition SemType : Type := value Empty_set → Prop.

(** Expression closure of a semantic type *)
Definition EClo (R : SemType) (e : expr Empty_set) :=
  ∃ v : value _, red_rtc e v ∧ R v.

(** Relation EClo R contains values of a semantic type R *)
Lemma EClo_value (R : SemType) v :
  R v → EClo R v.
Proof.
  intro Hv; eexists; split; [ constructor | assumption ].
Qed.

(** EClo is preserved by a backward reduction *)
Lemma EClo_red (R : SemType) e e' :
  red e e' → EClo R e' → EClo R e.
Proof.
  intros Hred [ v [ Hrtc Hv ] ].
  exists v; split; [ econstructor; eassumption | assumption ].
Qed.

(** EClo is preserved by backward many-step reduction *)
Lemma EClo_red_rtc (R : SemType) e e' :
  red_rtc e e' → EClo R e' → EClo R e.
Proof.
  induction 1; [ auto | ].
  intro; eapply EClo_red; eauto.
Qed.

(* ========================================================================= *)
(* Denotation of types *)

Reserved Notation "'⟦' τ '⟧'".

(* For convenience, for each type construct we define a corresponding
 * operation on semantic types *)

(** Semantic Unit type. Because we require a concrete shape of a value, it
  * is convenient to define this relation as an inductive type. *)
Inductive Rel_Unit : SemType :=
| RU_unit : Rel_Unit v_unit
.

(** Semantic Arrow type *)
Definition Rel_Arrow (R₁ R₂ : SemType) : SemType :=
  λ v, ∀ v', R₁ v' → EClo R₂ (e_app v v').

(** Denotation of types *)
Fixpoint relT (τ : type) : SemType :=
  match τ with
  | t_unit        => Rel_Unit
  | t_arrow τ₁ τ₂ => Rel_Arrow ⟦ τ₁ ⟧ ⟦ τ₂ ⟧
  end
where "⟦ τ ⟧" := (relT τ).

(** Denotation of typing environments *)
Definition rel_g {A : Set} (Γ : env A) (γ : A → value _) : Prop :=
  ∀ x, ⟦ Γ x ⟧ (γ x).

Notation "'G⟦' Γ '⟧'" := (@rel_g _ Γ).

(** The logical relation *)
Definition rel_e {A : Set} (Γ : env A) (e : expr A) (τ : type) : Prop :=
  ∀ γ, G⟦ Γ ⟧ γ → EClo ⟦ τ ⟧ (ebind γ e).

Notation "'T⟦' Γ '⊨' e '∷' τ '⟧'" := (@rel_e _ Γ e τ).

Lemma rel_g_env_ext {A : Set} (Γ : env A) (τ : type) γ v :
  G⟦ Γ ⟧ γ → ⟦ τ ⟧ v → G⟦ Γ[↦ τ ] ⟧ (γ [↦ v ]).
Proof.
  intros Hγ Hτ [ | x ]; simpl; [ assumption | apply Hγ ].
Qed.

(* ========================================================================= *)
(* Compatibility lemmas *)

Lemma compat_unit {A : Set} (Γ : env A) :
  T⟦ Γ ⊨ v_unit ∷ t_unit ⟧.
Proof.
  intros γ Hγ.
  apply EClo_value; constructor.
Qed.

Lemma compat_var {A : Set} (Γ : env A) x :
  T⟦ Γ ⊨ v_var x ∷ Γ x ⟧.
Proof.
  intros γ Hγ.
  apply EClo_value, Hγ.
Qed.

Lemma compat_lam {A : Set} (Γ : env A) e τ₁ τ₂ :
  T⟦ Γ [↦ τ₁ ] ⊨ e ∷ τ₂ ⟧ →
  T⟦ Γ ⊨ v_lam e ∷ t_arrow τ₁ τ₂ ⟧.
Proof.
  intros He γ Hγ; simpl.
  apply EClo_value.
  intros v Hv.
  eapply EClo_red; [ apply red_beta | ].
  rewrite esubst_bind_lift. (* we merge two substitutions *)
  apply He.
  apply rel_g_env_ext; assumption.
Qed.

(** Closed version of application copatibility *)
Lemma compat_app_cl e₁ e₂ (R₂ R₁ : SemType) :
  EClo (Rel_Arrow R₂ R₁) e₁ →
  EClo R₂ e₂ →
  EClo R₁ (e_app e₁ e₂).
Proof.
  intros [ v₁ [ He₁ Hv₁ ] ] [ v₂ [ He₂ Hv₂ ] ].
  eapply EClo_red_rtc; [ apply red_rtc_app1; eassumption | ].
  eapply EClo_red_rtc; [ apply red_rtc_app2; eassumption | ].
  apply Hv₁; assumption.
Qed.

Lemma compat_app {A : Set} (Γ : env A) e₁ e₂ τ₂ τ₁ :
  T⟦ Γ ⊨ e₁ ∷ t_arrow τ₂ τ₁ ⟧ →
  T⟦ Γ ⊨ e₂ ∷ τ₂ ⟧ →
  T⟦ Γ ⊨ e_app e₁ e₂ ∷ τ₁ ⟧.
Proof.
  intros He₁ He₂ γ Hγ; simpl.
  eapply compat_app_cl; [ eapply He₁ | eapply He₂ ]; assumption.
Qed.

(* ========================================================================= *)
(* Soundness *)

Theorem fundamental_property {A : Set} (Γ : env A) e τ :
  T[ Γ ⊢ e ∷ τ ] → T⟦ Γ ⊨ e ∷ τ ⟧.
Proof.
  induction 1.
  + apply compat_unit.
  + apply compat_var.
  + apply compat_lam; assumption.
  + eapply compat_app; eassumption.
Qed.

Theorem adequacy (R : SemType) e :
  EClo R e → ∃ v : value _, red_rtc e v.
Proof.
  intros [ v [ H _ ] ]; eauto.
Qed.

Theorem termination e τ :
  T[ env_empty ⊢ e ∷ τ ] → ∃ v : value _, red_rtc e v.
Proof.
  (* This is one of these rare cases where forward reasoning is more
   * convenient. *)
  intro He; apply fundamental_property in He.
  specialize (He v_var).
  rewrite ebind_pure' in He.
  eapply adequacy, He.
  intros [].
Qed.