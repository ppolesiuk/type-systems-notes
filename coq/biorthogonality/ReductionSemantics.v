(** We define a reduction semantics here. *)

Require Import Utf8.
Require Import Syntax.
Require Import Relation_Operators.

(** contraction relation *)
Inductive contr {V : Set} : expr V → expr V → Prop :=
| contr_beta : ∀ (e : expr _) (v : value V),
    contr (e_app (v_lam e) v) (esubst e v)
.

(** Reification of an evaluation context as a value. We shift context
  * (xshift E) since we use it in a larger scope of lambda-abstraction. *)
Definition reify_ectx {V : Set} (E : ectx V) : value V :=
  v_lam (e_abort (plug (xshift E) (v_var VZ))).

(** Reduction relation. Note that we have two non-local reductions. *)
Inductive red {V : Set} : program V → program V → Prop :=
| red_contr  : ∀ E e e',
    contr e e' →
    red (plug E e) (plug E e')
| red_callcc : ∀ E e,
    red (plug E (e_callcc e)) (plug E (esubst e (reify_ectx E)))
| red_abort : ∀ E p,
    red (plug E (e_abort p)) p
.

(** Reflexive and transitive closure of a reduction relation *)
Notation red_rtc e₁ e₂ := (clos_refl_trans_1n _ red e₁ e₂).