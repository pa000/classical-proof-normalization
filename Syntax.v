Require Import Utf8.
From TLC Require Import LibLN.

(* We use the locally nameless variable binding representation
   based on https://www.chargueraud.org/softs/ln/ *)

Inductive trm : Set :=
  | trm_bvar : nat → trm
  | trm_fvar : var → trm
  | trm_app  : trm → trm → trm
  | trm_abs  : trm → trm
  | trm_ctr  : trm → trm
  | trm_tp   : trm.

Fixpoint open_rec (k : nat) (u : trm) (t : trm) : trm :=
  match t with
  | trm_bvar i    => If k = i then u else trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_app t₁ t₂ => trm_app (open_rec k u t₁) (open_rec k u t₂)
  | trm_abs  t    => trm_abs (open_rec (S k) u t)
  | trm_ctr j     => trm_ctr (open_rec (S k) u j)
  | trm_tp        => trm_tp
  end.

Definition open t u := open_rec 0 u t.

Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x"  := (open t (trm_fvar x)).

Inductive term : trm → Prop :=
  | term_var : ∀ x,
      term (trm_fvar x)
  | term_app : ∀ t₁ t₂,
      term t₁ →
      term t₂ →
      term (trm_app t₁ t₂)
  | term_abs : ∀ L t,
      (∀ x, x \notin L → term (t ^ x)) →
      term (trm_abs t)
  | term_ctr : ∀ L t,
      (∀ x, x \notin L → term (t ^ x)) →
      term (trm_ctr t)
  | term_tp :
      term trm_tp.

Definition body t := ∃ L, ∀ x, x \notin L → term (t ^ x).

Inductive value : trm → Prop :=
  | value_abs : ∀ t,
      term (trm_abs t) → value (trm_abs t)
  | value_var : ∀ x,
      value (trm_fvar x).

Inductive jump : trm → Prop :=
  | jump_usr : ∀ k t,
      term t →
      jump (trm_app (trm_fvar k) t)
  | jump_tp : ∀ t,
      term t →
      jump (trm_app trm_tp t).

(* Substitution of a term in a jump. Used in reduction rules:
   red_C_L (J[k (P N) / k P]) and red_C_R (J[k (V P) / k P]) *)
Fixpoint jump_subst_rec (k : nat) (f : trm → trm) (t : trm) : trm :=
  match t with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_app (trm_bvar i) t =>
    If k = i then trm_app (trm_bvar i) (f t)
    else trm_app (trm_bvar i) (jump_subst_rec k f t)
  | trm_app t₁ t₂ => trm_app (jump_subst_rec k f t₁) (jump_subst_rec k f t₂)
  | trm_abs t     => trm_abs (jump_subst_rec (S k) f t)
  | trm_ctr j     => trm_ctr (jump_subst_rec (S k) f j)
  | trm_tp        => trm_tp
  end.

Definition jump_subst (t : trm) (f : trm → trm) : trm :=
  jump_subst_rec 0 f t.
