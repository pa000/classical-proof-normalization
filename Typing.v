Require Import Syntax.
Require Import Utf8.
From TLC Require Import LibLN.

Inductive type : Set :=
  | tp_bottom : type
  | tp_cont   : type
  | tp_arrow  : type → type → type.

Notation "⊥" := tp_bottom.
Notation "τ₁ → τ₂" := (tp_arrow τ₁ τ₂).

Reserved Notation "'T[' Γ '⊢' M '∷' A ']'".

Inductive typing (Γ : env type) : trm → type → Prop :=
  | T_Var : ∀ x A,
    ok Γ →
    binds x A Γ →
    T[ Γ ⊢ trm_fvar x ∷ A ]
  | T_Tp : ∀ M,
    T[ Γ ⊢ M ∷ ⊥ ] →
    T[ Γ ⊢ trm_app trm_tp M ∷ tp_cont ]
  | T_App : ∀ M M' A B,
    T[ Γ ⊢ M  ∷ A → B] →
    T[ Γ ⊢ M' ∷ A ] →
    T[ Γ ⊢ trm_app M M' ∷ B ]
  | T_Abs : ∀ L M A B,
    (∀ x, x \notin L →
      T[ Γ & x ~ A ⊢ M ^ x ∷ B ]) →
    T[ Γ ⊢ trm_abs M ∷ A → B]
  | T_Cont : ∀ k A M,
    T[ Γ ⊢ trm_fvar k ∷ A → tp_cont ] →
    T[ Γ ⊢ M ∷ A ] →
    T[ Γ ⊢ trm_app (trm_fvar k) M ∷ A ]
  | T_Ctrl : ∀ L A J,
    (∀ k, k \notin L →
      T[ Γ & k ~ (A → tp_cont) ⊢ J ^ k ∷ tp_cont ]) →
    T[ Γ ⊢ trm_ctr J ∷ A ]

where "T[ Γ ⊢ M ∷ A ]" := (typing Γ M A).