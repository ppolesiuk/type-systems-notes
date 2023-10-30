(** Here we define logical relation and prove fundamental property and
  * termination. *)

Require Import Utf8.
Require Import Syntax Typing ReductionSemantics.

(** Properties of Obs relation. Since biorthogonal logical relations are
 * modular we can use type-classes to prove soundness for every possible Obs
 * relation, that satisfies the following properties. *)
Class ObsClass (Obs : program Empty_set → Prop) : Prop :=
  { Obs_red : ∀ p p', red p p' → Obs p' → Obs p
  }.

Section LogRel.

(** Our logical relations are parametrized by Obs relation, that satisfies
  * some properties, describled by ObsClass. When we close the LogRel section,
  * the following two declarations became a parameters to definitions and
  * theorems of this section. *)
Variable Obs : program Empty_set → Prop.
Context {Obs_valid : ObsClass Obs}.

(* ========================================================================= *)
(* Biorthogonal closure *)

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

(** Semantic Unit type. Because we require a concrete shape of a value, it
  * is convenient to define this relation as an inductive type. *)
Inductive Rel_Unit : SemType :=
| RU_unit : Rel_Unit v_unit
.

(** Semantic Bottom type. *)
Inductive Rel_Bot : SemType :=
.

(** Semantic Arrow type *)
Definition Rel_Arrow (R₁ R₂ : SemType) : SemType :=
  λ v, ∀ v', R₁ v' → EClo R₂ (e_app v v').

(** Denotation of types *)
Fixpoint relT (τ : type) : SemType :=
  match τ with
  | t_unit        => Rel_Unit
  | t_bot         => Rel_Bot
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
  G⟦ Γ ⟧ γ → ⟦ τ ⟧ v → G⟦ Γ [↦ τ ] ⟧ (γ [↦ v ]).
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
  intros v Hv E HE.
  eapply Obs_red; [ apply red_contr, contr_beta | ].
  rewrite esubst_bind_lift. (* we merge two substitutions *)
  apply He; [ | exact HE ].
  apply rel_g_env_ext; assumption.
Qed.

(** Closed version of application copatibility. With biorthogonal logical
  * relations this proof is simple and beautiful. *)
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

Lemma compat_app {A : Set} (Γ : env A) e₁ e₂ τ₂ τ₁ :
  T⟦ Γ ⊨ e₁ ∷ t_arrow τ₂ τ₁ ⟧ →
  T⟦ Γ ⊨ e₂ ∷ τ₂ ⟧ →
  T⟦ Γ ⊨ e_app e₁ e₂ ∷ τ₁ ⟧.
Proof.
  intros He₁ He₂ γ Hγ; simpl.
  eapply compat_app_cl; [ eapply He₁ | eapply He₂ ]; assumption.
Qed.

Lemma compat_callcc {A : Set} (Γ : env A) e τ :
  T⟦ Γ [↦ t_arrow τ t_bot ] ⊨ e ∷ τ ⟧ →
  T⟦ Γ ⊨ e_callcc e ∷ τ ⟧.
Proof.
  (* Left as homework. Lemmas esubst_bind_lift, pbind_plug, xbind_scons_shift,
   * and xbind_pure' may turn out to be helpful here. *)
Admitted.

Lemma compat_absurd {A : Set} (Γ : env A) e τ :
  T⟦ Γ ⊨ e ∷ t_bot ⟧ →
  T⟦ Γ ⊨ e ∷ τ ⟧.
Proof.
  intros He γ Hγ E HE; simpl.
  apply He; [ assumption | ].
  intros v [].
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
  + apply compat_callcc; assumption.
  + apply compat_absurd; assumption.
Qed.

End LogRel.

(* We only prove termination. The type safety requires to prove that
 * the reduction is deterministic, which is standard, but not convenient
 * with the reduction semantics and inside-out contexts. *)

(* We start with instantiation of logical relations with termination property
 * as Obs. *)

Definition terminates (p : program Empty_set) : Prop :=
  ∃ v : value _, red_rtc p v.

#[local]
Instance ObsClass_terminates : ObsClass terminates.
Proof.
  split.
  + intros p p' Hred [ v Hrtc ].
    exists v; econstructor; eassumption.
Qed.

Theorem termination e τ :
  T[ env_empty ⊢ e ∷ τ ] → terminates e.
Proof.
  intro He.
  apply fundamental_property with (Obs:=terminates) in He;
    [ | exact ObsClass_terminates ].
  specialize (He v_var); rewrite ebind_pure' in He.
  unfold EClo in He; apply He with (E := ectx_hole).
  + intros [].
  + intros v _; exists v; constructor.
Qed.