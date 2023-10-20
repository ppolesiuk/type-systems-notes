(** Here, we prove type-soundness using logical relations. *)

Require Import Utf8.
Require Import Syntax SemanticsSOS Typing.

(** Semantic types: unary relations on closed values *)
Definition SemType : Type := value Empty_set → Prop.

(** Expression closure of a semantic type *)
Definition EClo (R : SemType) (e : expr Empty_set) :=
  ∀ e', red_rtc e e' →
    (∃ v : value _, R v ∧ e' = v) ∨
    (∃ e'', red e' e'').

(** Relation EClo R contains values of a semantic type R *)
Lemma EClo_value (R : SemType) v :
  R v → EClo R v.
Proof.
  intros Hv e; destruct 1 as [ | ? ? Hred ].
  + left; eauto.
  + (* impossible case: values don't reduce *)
    inversion Hred.
Qed.

(** EClo is preserved by a backward reduction *)
Lemma EClo_red (R : SemType) e e' :
  red e e' → EClo R e' → EClo R e.
Proof.
  intros Hred He' e₁ He₁.
  destruct He₁ as [ | e₂ e₃ Hred₁ ].
  + right; eauto.
  + apply He'.
    rewrite (red_deterministic Hred Hred₁); assumption.
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
  G⟦ Γ ⟧ γ → ⟦ τ ⟧ v → G⟦ env_ext Γ τ ⟧ (scons v γ).
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
  T⟦ env_ext Γ τ₁ ⊨ e ∷ τ₂ ⟧ →
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
  intros He₁ He₂ e Hred.
  destruct (red_rtc_app_inv Hred) as [ e₁' ? Hval | v₁ e₂' ? ? Hval | v₁ v₂ ].
  + right; specialize (He₁ e₁').
    destruct He₁ as [ [ v [ _ ? ] ] | [ e₁'' Hred₁ ] ];
      [ assumption | subst; exfalso; apply Hval; constructor | ].
    eexists; apply red_app1; eassumption.
  + right; specialize (He₂ e₂').
    destruct He₂ as [ [ v [ _ ? ] ] | [ e₂'' Hred₂ ] ];
      [ assumption | subst; exfalso; apply Hval; constructor | ].
    eexists; apply red_app2; eassumption.
  + specialize (He₁ v₁).
    destruct He₁ as [ [ v₁' [ Hv₁ Heq ] ] | [ ? Hred₁ ] ];
      [ assumption | | inversion Hred₁ ].
    injection Heq; clear Heq; intro; subst.
    specialize (He₂ v₂).
    destruct He₂ as [ [ v₂' [ Hv₂ Heq ] ] | [ ? Hred₂ ] ];
      [ assumption | | inversion Hred₂ ].
    injection Heq; clear Heq; intro; subst.
    eapply Hv₁; eassumption.
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
  EClo R e → safe e.
Proof.
  intros He e' Hred; specialize (He e' Hred).
  destruct He as [ [ v [ _ Heq ] ] | [ e'' Hred' ] ].
  + left; subst; constructor.
  + right; eauto.
Qed.

Theorem type_safety e τ :
  T[ env_empty ⊢ e ∷ τ ] → safe e.
Proof.
  (* This is one of these rare cases where forward reasoning is more
   * convenient. *)
  intro He; apply fundamental_property in He.
  specialize (He v_var).
  rewrite ebind_pure' in He.
  eapply adequacy, He.
  intros [].
Qed.