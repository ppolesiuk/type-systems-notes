(** This module contains the definition of syntax, together with basic
 * syntactic operations like substitution or variable renaming. *)

Require Import Utf8.

(** Adding one element to a type *)
Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.

Arguments VZ {V}.
Arguments VS {V}.

(** Extending function to inc domain (γ[↦v] operation) *)
Definition inc_ext {A : Set} {B : Type} (f : A → B) (v : B) (x : inc A) : B :=
  match x with
  | VZ   => v
  | VS y => f y
  end.

Notation "f '[↦' v ']'" := (@inc_ext _ _ f v) (at level 50).

(** Types *)
Inductive type : Set :=
| t_unit  : type
| t_arrow : type → type → type
.

(** Expressions and values *)
Inductive expr (V : Set) : Set :=
| e_value : value V → expr V
| e_app   : expr V → expr V → expr V

with value (V : Set) : Set :=
| v_var  : V → value V
| v_lam  : expr (inc V) → value V
| v_unit : value V
.

Arguments e_value {V}.
Arguments e_app   {V}.

Arguments v_var   {V}.
Arguments v_lam   {V}.
Arguments v_unit  {V}.

(* We register e_value as coercion in order to allow values in any context
 * where expressions are expected. *)
Coercion e_value : value >-> expr.

(* ========================================================================= *)
(* Mapping, i.e., variable renaming *)

(** Lifting of renamings (↑ operation) *)
Definition liftA {A B : Set} (f : A → B) (x : inc A) : inc B :=
  match x with
  | VZ   => VZ
  | VS y => VS (f y)
  end.

(** Mapping of expressions and values († operation) *)
Fixpoint emap {A B : Set} (f : A → B) (e : expr A) : expr B :=
  match e with
  | e_value   v => vmap f v
  | e_app e₁ e₂ => e_app (emap f e₁) (emap f e₂)
  end
with vmap {A B : Set} (f : A → B) (v : value A) : value B :=
  match v with
  | v_var x => v_var (f x)
  | v_lam e => v_lam (emap (liftA f) e)
  | v_unit  => v_unit
  end.

(** Shifting of expressions (s† operation). This operation shifts expression
  * to a context where one more variable is allowed *)
Definition eshift {A : Set} (e : expr A) : expr (inc A) := emap VS e.

(** Shifting of values *)
Definition vshift {A : Set} (v : value A) : value (inc A) := vmap VS v.

(* ========================================================================= *)
(* Binding, i.e., simultaneous substitution *)

(** Lifting of substitution (⇑ operation) *)
Definition liftS {A B : Set} (f : A → value B) (x : inc A) : value (inc B) :=
  match x with
  | VZ   => v_var VZ
  | VS y => vshift (f y)
  end.

(** Binding of expressions and value ( * operation) *)
Fixpoint ebind {A B : Set} (f : A → value B) (e : expr A) : expr B :=
  match e with
  | e_value   v => vbind f v
  | e_app e₁ e₂ => e_app (ebind f e₁) (ebind f e₂)
  end
with vbind {A B : Set} (f : A → value B) (v : value A) : value B :=
  match v with
  | v_var x => f x
  | v_lam e => v_lam (ebind (liftS f) e)
  | v_unit  => v_unit
  end.

(** Substitution of single value in expression *)
Definition esubst {A : Set} (e : expr (inc A)) (v : value A) : expr A :=
  ebind (v_var [↦ v ]) e.

(** Substitution of single value in value *)
Definition vsubst {A : Set} (v' : value (inc A)) (v : value A) : value A :=
  vbind (v_var [↦ v ]) v'.

(* ========================================================================= *)
(* Properties of variable renamings *)

Lemma liftA_id {A : Set} (f : A → A) :
  (∀ x, f x = x) →
  (∀ x, liftA f x = x).
Proof.
  intros Hf [ | x ]; simpl.
  + reflexivity.
  + f_equal; apply Hf.
Qed.

Lemma liftA_liftA_comp {A B C : Set}
  (f : B → C) (g : A → B) (h : A → C) :
  (∀ x, f (g x) = h x) →
  ∀ x, liftA f (liftA g x) = liftA h x.
Proof.
  intros Hf [ | x ]; simpl.
  + reflexivity.
  + f_equal; apply Hf.
Qed.

Fixpoint emap_id {A : Set} (f : A → A) e :
  (∀ x, f x = x) →
  emap f e = e
with vmap_id {A : Set} (f : A → A) v :
  (∀ x, f x = x) →
  vmap f v = v.
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply emap_id || apply vmap_id;
    try apply liftA_id; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply emap_id || apply vmap_id;
    try apply liftA_id; assumption.
Qed.

Lemma emap_id' {A : Set} (e : expr A) :
  emap (λ x, x) e = e.
Proof.
  apply emap_id; reflexivity.
Qed.

Lemma vmap_id' {A : Set} (v : value A) :
  vmap (λ x, x) v = v.
Proof.
  apply vmap_id; reflexivity.
Qed.

Fixpoint emap_map_comp {A B C : Set}
  (f : B → C) (g : A → B) (h : A → C) e :
  (∀ x, f (g x) = h x) →
  emap f (emap g e) = emap h e
with vmap_map_comp {A B C : Set}
  (f : B → C) (g : A → B) (h : A → C) v :
  (∀ x, f (g x) = h x) →
  vmap f (vmap g v) = vmap h v.
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply emap_map_comp || apply vmap_map_comp;
    try apply liftA_liftA_comp; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply emap_map_comp || apply vmap_map_comp;
    try apply liftA_liftA_comp; assumption.
Qed.

Lemma emap_map_comp' {A B C : Set}
  (f : B → C) (g : A → B) e :
  emap f (emap g e) = emap (λ x, f (g x)) e.
Proof.
  apply emap_map_comp; reflexivity.
Qed.

Lemma vmap_map_comp' {A B C : Set}
  (f : B → C) (g : A → B) v :
  vmap f (vmap g v) = vmap (λ x, f (g x)) v.
Proof.
  apply vmap_map_comp; reflexivity.
Qed.

Lemma eshift_map {A B : Set} (f : A → B) e :
  eshift (emap f e) = emap (liftA f) (eshift e).
Proof.
  unfold eshift; erewrite emap_map_comp' with (g := VS).
  apply emap_map_comp; reflexivity.
Qed.

Lemma vshift_map {A B : Set} (f : A → B) v :
  vshift (vmap f v) = vmap (liftA f) (vshift v).
Proof.
  unfold vshift; erewrite vmap_map_comp' with (g := VS).
  apply vmap_map_comp; reflexivity.
Qed.

(* ========================================================================= *)
(* Properties of simultaneous substitutions *)

Lemma liftS_liftA_comp {A B C D : Set}
  (f₁ : B → value D) (g₁ : A → B) (g₂ : C → D) (f₂ : A → value C) :
  (∀ x, f₁ (g₁ x) = vmap g₂ (f₂ x)) →
  ∀ x, liftS f₁ (liftA g₁ x) = vmap (liftA g₂) (liftS f₂ x).
Proof.
  intros Hf [ | x ]; simpl.
  + reflexivity.
  + rewrite Hf; apply vshift_map.
Qed.

Fixpoint ebind_map_comp {A B C D : Set}
  (f₁ : B → value D) (g₁ : A → B) (g₂ : C → D) (f₂ : A → value C) e :
  (∀ x, f₁ (g₁ x) = vmap g₂ (f₂ x)) →
  ebind f₁ (emap g₁ e) = emap g₂ (ebind f₂ e)
with vbind_map_comp {A B C D : Set}
  (f₁ : B → value D) (g₁ : A → B) (g₂ : C → D) (f₂ : A → value C) v :
  (∀ x, f₁ (g₁ x) = vmap g₂ (f₂ x)) →
  vbind f₁ (vmap g₁ v) = vmap g₂ (vbind f₂ v).
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply ebind_map_comp || apply vbind_map_comp;
    try apply liftS_liftA_comp; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply ebind_map_comp || apply vbind_map_comp;
    try apply liftS_liftA_comp; assumption.
Qed.

Lemma liftS_pure {A : Set} (f : A → value A) :
  (∀ x, f x = v_var x) →
  ∀ x, liftS f x = v_var x.
Proof.
  intros Hf [ | x ]; simpl.
  + reflexivity.
  + rewrite Hf; reflexivity.
Qed.

Lemma liftS_liftS_comp {A B C : Set}
  (f : B → value C) (g : A → value B) (h : A → value C) :
  (∀ x, vbind f (g x) = h x) →
  ∀ x, vbind (liftS f) (liftS g x) = liftS h x.
Proof.
  intros Hf [ | x ]; simpl.
  + reflexivity.
  + rewrite <- Hf;
    apply vbind_map_comp; reflexivity.
Qed.

Fixpoint ebind_pure {A : Set} (f : A → value A) e :
  (∀ x, f x = v_var x) →
  ebind f e = e
with vbind_pure {A : Set} (f : A → value A) v :
  (∀ x, f x = v_var x) →
  vbind f v = v.
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply ebind_pure || apply vbind_pure;
    try apply liftS_pure; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply ebind_pure || apply vbind_pure;
    try apply liftS_pure; assumption.
Qed.

Lemma ebind_pure' {A : Set} (e : expr A) :
  ebind v_var e = e.
Proof.
  apply ebind_pure; reflexivity.
Qed.

Lemma vbind_pure' {A : Set} (v : value A) :
  vbind v_var v = v.
Proof.
  apply vbind_pure; reflexivity.
Qed.

Fixpoint ebind_bind_comp {A B C : Set}
  (f : B → value C) (g : A → value B) (h : A → value C) e :
  (∀ x, vbind f (g x) = h x) →
  ebind f (ebind g e) = ebind h e
with vbind_bind_comp {A B C : Set}
  (f : B → value C) (g : A → value B) (h : A → value C) v :
  (∀ x, vbind f (g x) = h x) →
  vbind f (vbind g v) = vbind h v.
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply ebind_bind_comp || apply vbind_bind_comp;
    try apply liftS_liftS_comp; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply ebind_bind_comp || apply vbind_bind_comp;
    try apply liftS_liftS_comp; assumption.
Qed.

(* ========================================================================= *)
(* Properties of subtitutions *)

Lemma esubst_shift {A : Set} (e : expr A) v :
  esubst (eshift e) v = e.
Proof.
  unfold esubst, eshift.
  rewrite ebind_map_comp with (g₂ := λ x, x) (f₂ := v_var);
    [ | reflexivity ].
  rewrite emap_id'; apply ebind_pure'.
Qed.

Lemma vsubst_shift {A : Set} (v' : value A) v :
  vsubst (vshift v') v = v'.
Proof.
  unfold vsubst, vshift.
  rewrite vbind_map_comp with (g₂ := λ x, x) (f₂ := v_var);
    [ | reflexivity ].
  rewrite vmap_id'; apply vbind_pure'.
Qed.

Lemma esubst_bind_lift {A B : Set} (f : A → value B) e v :
  esubst (ebind (liftS f) e) v = ebind (f [↦ v ]) e.
Proof.
  apply ebind_bind_comp.
  intros [ | x ]; simpl; [ reflexivity | ].
  apply vsubst_shift.
Qed.

Lemma vsubst_bind_lift {A B : Set} (f : A → value B) v' v :
  vsubst (vbind (liftS f) v') v = vbind (f [↦ v ]) v'.
Proof.
  apply vbind_bind_comp.
  intros [ | x ]; simpl; [ reflexivity | ].
  apply vsubst_shift.
Qed.