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

(** Types *)
Inductive type : Set :=
| t_unit  : type
| t_bot   : type
| t_arrow : type → type → type
.


(** Expressions, values, and programs *)
Inductive expr (V : Set) : Set :=
| e_value  : value V → expr V
| e_app    : expr V → expr V → expr V
| e_callcc : expr (inc V) → expr V
| e_abort  : program V → expr V

with value (V : Set) : Set :=
| v_var  : V → value V
| v_lam  : expr (inc V) → value V
| v_unit : value V

with program (V : Set) : Set :=
| p_expr : expr V → program V
.

Arguments e_value  {V}.
Arguments e_app    {V}.
Arguments e_callcc {V}.
Arguments e_abort  {V}.

Arguments v_var   {V}.
Arguments v_lam   {V}.
Arguments v_unit  {V}.

Arguments p_expr {V}.

(* We register e_value as coercion in order to allow values in any context
 * where expressions are expected. *)
Coercion e_value : value >-> expr.
(* We do the same for p_expr *)
Coercion p_expr : expr >-> program.

(** Inside-out evaluation contexts *)
Inductive ectx (V : Set) : Set :=
| ectx_hole   : ectx V
| ectx_app1   : ectx V → expr V → ectx V
| ectx_app2   : value V → ectx V → ectx V
.

Arguments ectx_hole   {V}.
Arguments ectx_app1   {V}.
Arguments ectx_app2   {V}.

(** Plugging expression into an evaluation context (inside-out) *)
Fixpoint plug {V : Set} (E : ectx V) (e : expr V) : program V :=
  match E with
  | ectx_hole      => e
  | ectx_app1 E e' => plug E (e_app e e')
  | ectx_app2 v E  => plug E (e_app v e)
  end.

(* ========================================================================= *)
(* Mapping, i.e., variable renaming *)

(** Lifting of renamings (↑ operation) *)
Definition liftA {A B : Set} (f : A → B) (x : inc A) : inc B :=
  match x with
  | VZ   => VZ
  | VS y => VS (f y)
  end.

(** Mapping of expressions, values, and programs († operation) *)
Fixpoint emap {A B : Set} (f : A → B) (e : expr A) : expr B :=
  match e with
  | e_value   v => vmap f v
  | e_app e₁ e₂ => e_app (emap f e₁) (emap f e₂)
  | e_callcc e  => e_callcc (emap (liftA f) e)
  | e_abort  e  => e_abort (pmap f e)
  end
with vmap {A B : Set} (f : A → B) (v : value A) : value B :=
  match v with
  | v_var x => v_var (f x)
  | v_lam e => v_lam (emap (liftA f) e)
  | v_unit  => v_unit
  end
with pmap {A B : Set} (f : A → B) (p : program A) : program B :=
  match p with
  | p_expr e => p_expr (emap f e)
  end.

(** Mapping of evaluation contexts *)
Fixpoint xmap {A B : Set} (f : A → B) (E : ectx A) : ectx B :=
  match E with
  | ectx_hole     => ectx_hole
  | ectx_app1 E e => ectx_app1 (xmap f E) (emap f e)
  | ectx_app2 v E => ectx_app2 (vmap f v) (xmap f E)
  end.

(** Shifting of expressions (s† operation). This operation shifts expression
  * to a context where one more variable is allowed *)
Definition eshift {A : Set} (e : expr A) : expr (inc A) := emap VS e.

(** Shifting of values *)
Definition vshift {A : Set} (v : value A) : value (inc A) := vmap VS v.

(** Shifting of evaluation contexts *)
Definition xshift {A : Set} (E : ectx A) : ectx (inc A) := xmap VS E.

(* ========================================================================= *)
(* Binding, i.e., simultaneous substitution *)

(** Lifting of substitution (⇑ operation) *)
Definition liftS {A B : Set} (f : A → value B) (x : inc A) : value (inc B) :=
  match x with
  | VZ   => v_var VZ
  | VS y => vshift (f y)
  end.

(** Binding of expressions, values, and programs ( * operation) *)
Fixpoint ebind {A B : Set} (f : A → value B) (e : expr A) : expr B :=
  match e with
  | e_value   v => vbind f v
  | e_app e₁ e₂ => e_app (ebind f e₁) (ebind f e₂)
  | e_callcc e  => e_callcc (ebind (liftS f) e)
  | e_abort  p  => e_abort (pbind f p)
  end
with vbind {A B : Set} (f : A → value B) (v : value A) : value B :=
  match v with
  | v_var x => f x
  | v_lam e => v_lam (ebind (liftS f) e)
  | v_unit  => v_unit
  end
with pbind {A B : Set} (f : A → value B) (p : program A) : program B :=
  match p with
  | p_expr e => p_expr (ebind f e)
  end.

(** Binding of evaluation contexts *)
Fixpoint xbind {A B : Set} (f : A → value B) (E : ectx A) : ectx B :=
  match E with
  | ectx_hole     => ectx_hole
  | ectx_app1 E e => ectx_app1 (xbind f E) (ebind f e)
  | ectx_app2 v E => ectx_app2 (vbind f v) (xbind f E)
  end.

(** Extending substitution (◃ operation) *)
Definition scons {A B : Set} (v : value B) (f : A → value B) (x : inc A) :
    value B :=
  match x with
  | VZ   => v
  | VS y => f y
  end.

(** Substitution of single value in expression *)
Definition esubst {A : Set} (e : expr (inc A)) (v : value A) : expr A :=
  ebind (scons v v_var) e.

(** Substitution of single value in value *)
Definition vsubst {A : Set} (v' : value (inc A)) (v : value A) : value A :=
  vbind (scons v v_var) v'.

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
  vmap f v = v
with pmap_id {A : Set} (f : A → A) p :
  (∀ x, f x = x) →
  pmap f p = p.
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply emap_id || apply vmap_id || apply pmap_id;
    try apply liftA_id; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply emap_id || apply vmap_id;
    try apply liftA_id; assumption.
+ intro Hf; destruct p; simpl; f_equal;
    apply emap_id; assumption.
Qed.

Fixpoint xmap_id {A : Set} (f : A → A) E :
  (∀ x, f x = x) →
  xmap f E = E.
Proof.
  intro Hf; destruct E; simpl; f_equal;
    apply emap_id || apply vmap_id || apply xmap_id;
    assumption.
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

Lemma xmap_id' {A : Set} (E : ectx A) :
  xmap (λ x, x) E = E.
Proof.
  apply xmap_id; reflexivity.
Qed.

Fixpoint emap_map_comp {A B C : Set}
  (f : B → C) (g : A → B) (h : A → C) e :
  (∀ x, f (g x) = h x) →
  emap f (emap g e) = emap h e
with vmap_map_comp {A B C : Set}
  (f : B → C) (g : A → B) (h : A → C) v :
  (∀ x, f (g x) = h x) →
  vmap f (vmap g v) = vmap h v
with pmap_map_comp {A B C : Set}
  (f : B → C) (g : A → B) (h : A → C) p :
  (∀ x, f (g x) = h x) →
  pmap f (pmap g p) = pmap h p.
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply emap_map_comp || apply vmap_map_comp || apply pmap_map_comp;
    try apply liftA_liftA_comp; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply emap_map_comp || apply vmap_map_comp;
    try apply liftA_liftA_comp; assumption.
+ intro Hf; destruct p; simpl; f_equal;
    apply emap_map_comp; assumption.
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

Lemma pbind_plug {A B : Set} (f : A → value B) E e :
  pbind f (plug E e) = plug (xbind f E) (ebind f e).
Proof.
  generalize e; clear e; induction E; intro; simpl; try reflexivity;
    apply IHE.
Qed.

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
  vbind f₁ (vmap g₁ v) = vmap g₂ (vbind f₂ v)
with pbind_map_comp {A B C D : Set}
  (f₁ : B → value D) (g₁ : A → B) (g₂ : C → D) (f₂ : A → value C) p :
  (∀ x, f₁ (g₁ x) = vmap g₂ (f₂ x)) →
  pbind f₁ (pmap g₁ p) = pmap g₂ (pbind f₂ p).
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply ebind_map_comp || apply vbind_map_comp || apply pbind_map_comp;
    try apply liftS_liftA_comp; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply ebind_map_comp || apply vbind_map_comp;
    try apply liftS_liftA_comp; assumption.
+ intro Hf; destruct p; simpl; f_equal;
    apply ebind_map_comp; assumption.
Qed.

Fixpoint xbind_map_comp {A B C D : Set}
  (f₁ : B → value D) (g₁ : A → B) (g₂ : C → D) (f₂ : A → value C) E :
  (∀ x, f₁ (g₁ x) = vmap g₂ (f₂ x)) →
  xbind f₁ (xmap g₁ E) = xmap g₂ (xbind f₂ E).
Proof.
  intro Hf; destruct E; simpl; f_equal;
    apply ebind_map_comp || apply vbind_map_comp || apply xbind_map_comp;
    assumption.
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
  vbind f v = v
with pbind_pure {A : Set} (f : A → value A) p :
  (∀ x, f x = v_var x) →
  pbind f p = p.
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply ebind_pure || apply vbind_pure || apply pbind_pure;
    try apply liftS_pure; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply ebind_pure || apply vbind_pure;
    try apply liftS_pure; assumption.
+ intro Hf; destruct p; simpl; f_equal;
    apply ebind_pure; assumption.
Qed.

Fixpoint xbind_pure {A : Set} (f : A → value A) E :
  (∀ x, f x = v_var x) →
  xbind f E = E.
Proof.
  intro Hf; destruct E; simpl; f_equal;
    apply ebind_pure || apply vbind_pure || apply xbind_pure;
    assumption.
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

Lemma xbind_pure' {A : Set} (E : ectx A) :
  xbind v_var E = E.
Proof.
  apply xbind_pure; reflexivity.
Qed.

Fixpoint ebind_bind_comp {A B C : Set}
  (f : B → value C) (g : A → value B) (h : A → value C) e :
  (∀ x, vbind f (g x) = h x) →
  ebind f (ebind g e) = ebind h e
with vbind_bind_comp {A B C : Set}
  (f : B → value C) (g : A → value B) (h : A → value C) v :
  (∀ x, vbind f (g x) = h x) →
  vbind f (vbind g v) = vbind h v
with pbind_bind_comp {A B C : Set}
  (f : B → value C) (g : A → value B) (h : A → value C) p :
  (∀ x, vbind f (g x) = h x) →
  pbind f (pbind g p) = pbind h p.
Proof.
+ intro Hf; destruct e; simpl; f_equal;
    apply ebind_bind_comp || apply vbind_bind_comp || apply pbind_bind_comp;
    try apply liftS_liftS_comp; assumption.
+ intro Hf; destruct v; simpl; f_equal;
    apply Hf || apply ebind_bind_comp || apply vbind_bind_comp;
    try apply liftS_liftS_comp; assumption.
+ intro Hf; destruct p; simpl; f_equal;
    apply ebind_bind_comp; assumption.
Qed.

Fixpoint xbind_bind_comp {A B C : Set}
  (f : B → value C) (g : A → value B) (h : A → value C) E :
  (∀ x, vbind f (g x) = h x) →
  xbind f (xbind g E) = xbind h E.
Proof.
  intro Hf; destruct E; simpl; f_equal;
    apply ebind_bind_comp || apply vbind_bind_comp || apply xbind_bind_comp;
    assumption.
Qed.

Lemma ebind_scons_shift {A B : Set} v (f : A → value B) e :
  ebind (scons v f) (eshift e) = ebind f e.
Proof.
  unfold eshift.
  erewrite ebind_map_comp; [ apply emap_id' | ].
  symmetry; apply vmap_id'.
Qed.

Lemma vbind_scons_shift {A B : Set} v' (f : A → value B) v :
  vbind (scons v' f) (vshift v) = vbind f v.
Proof.
  unfold vshift.
  erewrite vbind_map_comp; [ apply vmap_id' | ].
  symmetry; apply vmap_id'.
Qed.

Lemma xbind_scons_shift {A B : Set} v (f : A → value B) E :
  xbind (scons v f) (xshift E) = xbind f E.
Proof.
  unfold xshift.
  erewrite xbind_map_comp; [ apply xmap_id' | ].
  symmetry; apply vmap_id'.
Qed.

(* ========================================================================= *)
(* Properties of subtitutions *)

Lemma esubst_shift {A : Set} (e : expr A) v :
  esubst (eshift e) v = e.
Proof.
  unfold esubst; rewrite ebind_scons_shift; apply ebind_pure'.
Qed.

Lemma vsubst_shift {A : Set} (v' : value A) v :
  vsubst (vshift v') v = v'.
Proof.
  unfold vsubst; rewrite vbind_scons_shift; apply vbind_pure'.
Qed.

Lemma esubst_bind_lift {A B : Set} (f : A → value B) e v :
  esubst (ebind (liftS f) e) v = ebind (scons v f) e.
Proof.
  apply ebind_bind_comp.
  intros [ | x ]; simpl; [ reflexivity | ].
  apply vsubst_shift.
Qed.

Lemma vsubst_bind_lift {A B : Set} (f : A → value B) v' v :
  vsubst (vbind (liftS f) v') v = vbind (scons v f) v'.
Proof.
  apply vbind_bind_comp.
  intros [ | x ]; simpl; [ reflexivity | ].
  apply vsubst_shift.
Qed.