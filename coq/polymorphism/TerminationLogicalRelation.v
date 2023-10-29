(** Here, we prove a termination property using logical relations. *)

Require Import Utf8.
Require Import Syntax Typing SemanticsSOS.
Require Import RelationClasses.

(** We observe just a termination. *)
Definition Obs (e : expr Empty_set) : Prop :=
  ∃ v : value _, red_rtc e v.

Lemma Obs_red e e' : red e e' → Obs e' → Obs e.
Proof.
  intros Hred [ v Hrtc ]; exists v.
  econstructor; eassumption.
Qed.

(** Semantic types: unary relations on closed values *)
Definition SemType : Type := value Empty_set → Prop.

(** Closure for evaluation contexts *)
Definition KClo (R : SemType) (E : ectx Empty_set) : Prop :=
  ∀ v : value _, R v → Obs (plug E v).

(** Biorthogonal closure *)
Definition EClo (R : SemType) (e : expr Empty_set) : Prop :=
  ∀ E : ectx _, KClo R E → Obs (plug E e).

(** Relation EClo R contains values of a semantic type R *)
Lemma EClo_value (R : SemType) v :
  R v → EClo R v.
Proof.
  intros Hv E HE; apply HE, Hv.
Qed.

(* ========================================================================= *)
(* Denotation of types *)

Reserved Notation "'⟦' τ '⟧'".

(* For convenience, for each type construct we define a corresponding
 * operation on semantic types *)

(** Semantic Arrow type *)
Definition Rel_Arrow (R₁ R₂ : SemType) : SemType :=
  λ v, ∀ v', R₁ v' → EClo R₂ (e_app v v').

(** Semantic universal type. *)
Definition Rel_Forall (F : SemType → SemType) : SemType :=
  λ v, ∀ R : SemType, EClo (F R) (e_tapp v).

(** Denotation of types *)
Fixpoint relT {Δ : Set} (τ : type Δ) (η : Δ → SemType) : SemType :=
  match τ with
  | t_var   α     => η α
  | t_arrow τ₁ τ₂ => Rel_Arrow (⟦ τ₁ ⟧ η) (⟦ τ₂ ⟧ η)
  | t_forall τ    => Rel_Forall (λ R, ⟦ τ ⟧ (scons R η))
  end
where "⟦ τ ⟧" := (@relT _ τ).

(** Denotation of typing environments *)
Definition rel_g {Δ A : Set}
    (Γ : env Δ A) (η : Δ → SemType) (γ : A → value _) : Prop :=
  ∀ x, ⟦ Γ x ⟧ η (γ x).

Notation "'G⟦' Γ '⟧'" := (@rel_g _ _ Γ).

(** The logical relation *)
Definition rel_e {Δ A : Set} (Γ : env Δ A) (e : expr A) (τ : type Δ) : Prop :=
  ∀ η γ, G⟦ Γ ⟧ η γ → EClo (⟦ τ ⟧ η) (ebind γ e).

Notation "'T⟦' Γ '⊨' e '∷' τ '⟧'" := (@rel_e _ _ Γ e τ).

(* ========================================================================= *)
(* Weakening and substitution lemmas *)

(* We start with some helper lemmas for proving logical equivalences *)
Lemma forall_equiv {A : Type} (F₁ F₂ : A → Prop) :
  (∀ x, F₁ x ↔ F₂ x) →
  (∀ x, F₁ x) ↔ (∀ x, F₂ x).
Proof. firstorder. Qed.

Lemma imp_equiv (P₁ P₂ Q₁ Q₂ : Prop) :
  (P₁ ↔ P₂) → (Q₁ ↔ Q₂) → (P₁ → Q₁) ↔ (P₂ → Q₂).
Proof. tauto. Qed.

(** EClo preserves equivalence of relations *)
Lemma EClo_equiv (R₁ R₂ : SemType) e :
  (∀ v, R₁ v ↔ R₂ v) → EClo R₁ e ↔ EClo R₂ e.
Proof.
  intro HR.
  apply forall_equiv; intro E.
  apply imp_equiv; [ | reflexivity ].
  apply forall_equiv; intro v.
  apply imp_equiv; [ | reflexivity ].
  apply HR.
Qed.

(** Weakening lemma (in a slightly more general form) *)
Lemma relT_map {Δ₁ Δ₂ : Set} (f : Δ₁ → Δ₂)
    (η₁ : Δ₁ → SemType) (η₂ : Δ₂ → SemType) τ v :
  (∀ α v, η₁ α v ↔ η₂ (f α) v) →
  ⟦ τ ⟧ η₁ v ↔ ⟦ tmap f τ ⟧ η₂ v.
Proof.
  (* Left as an exercise. Try to not split the equivalence (↔), but use the
   * lemmas proven above. *)
Admitted.

(** Weakening lemma *)
Lemma relT_weaken {Δ : Set} (η : Δ → SemType) τ R v :
  ⟦ τ ⟧ η v ↔ ⟦ tshift τ ⟧ (scons R η) v.
Proof.
  apply relT_map; reflexivity.
Qed.

(** Substitution lemma (in a slightly more general form) *)
Lemma relT_bind {Δ₁ Δ₂ : Set} (f : Δ₁ → type Δ₂)
    (η₁ : Δ₁ → SemType) (η₂ : Δ₂ → SemType) τ v :
  (∀ α v, η₁ α v ↔ ⟦ f α ⟧ η₂ v) →
  ⟦ τ ⟧ η₁ v ↔ ⟦ tbind f τ ⟧ η₂ v.
Proof.
  (* Left as an exercise *)
Admitted.

(** Substitution lemma *)
Lemma relT_subst {Δ : Set} (η : Δ → SemType) τ τ' v :
  ⟦ τ ⟧ (scons (⟦ τ' ⟧ η) η) v ↔ ⟦ tsubst τ τ' ⟧ η v.
Proof.
  apply relT_bind; intros []; reflexivity.
Qed.

(* ========================================================================= *)
(* Changing the typing environment *)

Lemma rel_g_env_ext {Δ A : Set} (Γ : env Δ A) (τ : type Δ) η γ v :
  G⟦ Γ ⟧ η γ → ⟦ τ ⟧ η v → G⟦ env_ext Γ τ ⟧ η (scons v γ).
Proof.
  intros Hγ Hτ [ | x ]; simpl; [ assumption | apply Hγ ].
Qed.

Lemma rel_g_env_shift {Δ A : Set} (Γ : env Δ A) η γ R :
  G⟦ Γ ⟧ η γ → G⟦ env_shift Γ ⟧ (scons R η) γ.
Proof.
  intros Hγ x; simpl.
  apply relT_weaken, Hγ.
Qed.

(* ========================================================================= *)
(* Compatibility lemmas *)

Lemma compat_var {Δ A : Set} (Γ : env Δ A) x :
  T⟦ Γ ⊨ v_var x ∷ Γ x ⟧.
Proof.
  intros η γ Hγ.
  apply EClo_value, Hγ.
Qed.

Lemma compat_lam {Δ A : Set} (Γ : env Δ A) e τ₁ τ₂ :
  T⟦ env_ext Γ τ₁ ⊨ e ∷ τ₂ ⟧ →
  T⟦ Γ ⊨ v_lam e ∷ t_arrow τ₁ τ₂ ⟧.
Proof.
  intros He η γ Hγ; simpl.
  apply EClo_value.
  intros v Hv E HE.
  eapply Obs_red; [ apply red_in_ectx; constructor | ].
  rewrite esubst_bind_lift. (* we merge two substitutions *)
  eapply He; [ | exact HE ].
  apply rel_g_env_ext; assumption.
Qed.

Lemma compat_tlam {Δ A : Set} (Γ : env Δ A) e τ :
  T⟦ env_shift Γ ⊨ e ∷ τ ⟧ →
  T⟦ Γ ⊨ v_tlam e ∷ t_forall τ ⟧.
Proof.
  (* Left as an exercise. Lemma rel_g_env_shift might be useful. *)
Admitted.

(** Closed version of application copatibility. *)
Lemma compat_app_cl e₁ e₂ (R₂ R₁ : SemType) :
  EClo (Rel_Arrow R₂ R₁) e₁ →
  EClo R₂ e₂ →
  EClo R₁ (e_app e₁ e₂).
Proof.
  intros He₁ He₂ E HE.
  change (Obs (plug (ectx_app1 E e₂) e₁)).
  apply He₁; intros v₁ Hv₁.
  change (Obs (plug (ectx_app2 v₁ E) e₂)).
  apply He₂; intros v₂ Hv₂.
  change (Obs (plug E (e_app v₁ v₂))).
  apply Hv₁; assumption.
Qed.

Lemma compat_app {Δ A : Set} (Γ : env Δ A) e₁ e₂ τ₂ τ₁ :
  T⟦ Γ ⊨ e₁ ∷ t_arrow τ₂ τ₁ ⟧ →
  T⟦ Γ ⊨ e₂ ∷ τ₂ ⟧ →
  T⟦ Γ ⊨ e_app e₁ e₂ ∷ τ₁ ⟧.
Proof.
  intros He₁ He₂ η γ Hγ; simpl.
  eapply compat_app_cl; [ eapply He₁ | eapply He₂ ]; assumption.
Qed.

Lemma compat_tapp {Δ A : Set} (Γ : env Δ A) e τ τ' :
  T⟦ Γ ⊨ e ∷ t_forall τ ⟧ →
  T⟦ Γ ⊨ e_tapp e ∷ tsubst τ τ' ⟧.
Proof.
  (* Left as an exercise. *)
Admitted.

(* ========================================================================= *)
(* Soundness *)

Theorem fundamental_property {Δ A : Set} (Γ : env Δ A) e τ :
  T[ Γ ⊢ e ∷ τ ] → T⟦ Γ ⊨ e ∷ τ ⟧.
Proof.
  induction 1.
  + apply compat_var.
  + apply compat_lam; assumption.
  + apply compat_tlam; assumption.
  + eapply compat_app; eassumption.
  + apply compat_tapp; assumption.
Qed.

Theorem adequacy e τ :
  T⟦ env_empty ⊨ e ∷ τ ⟧ → ∃ v : value _, red_rtc e v.
Proof.
  intro He.
  specialize (He (λ x : Empty_set, match x with end) v_var).
  rewrite ebind_pure' in He.
  unfold EClo in He.
  apply He with (E := ectx_hole); [ intros [] | ].
  intros v _; exists v; constructor.
Qed.

Theorem termination e τ :
  T[ env_empty ⊢ e ∷ τ ] → ∃ v : value _, red_rtc e v.
Proof.
  intro He; apply fundamental_property, adequacy in He.
  assumption.
Qed.