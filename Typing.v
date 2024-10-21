Require Import Syntax.
Require Import Utf8.
From TLC Require Import LibLN.

Inductive type : Set :=
  | tp_bottom : type
  | tp_cont   : type → type
  | tp_arrow  : type → type → type.

Notation "⊥" := tp_bottom.
Notation "A → B" := (tp_arrow A B).

Reserved Notation "'T[' Γ '⊢' M '∷' A ']'".
Reserved Notation "'J[' Γ '⊢' J ']'".

Inductive typing : env type → trm → type → Prop :=
  | T_Var : ∀ Γ x A,
    ok Γ →
    binds x A Γ →
    T[ Γ ⊢ trm_fvar x ∷ A ]
  | T_App : ∀ Γ M M' A B,
    T[ Γ ⊢ M  ∷ A → B ] →
    T[ Γ ⊢ M' ∷ A ] →
    T[ Γ ⊢ trm_app M M' ∷ B ]
  | T_Abs : ∀ Γ L M A B,
    (∀ x, x \notin L →
      T[ Γ & x ~ A ⊢ M ^ x ∷ B ]) →
    T[ Γ ⊢ trm_abs M ∷ A → B ]
  | T_Ctrl : ∀ Γ L A J,
    (∀ k, k \notin L →
      J[ Γ & k ~ (tp_cont A) ⊢ J ^ k ]) →
    T[ Γ ⊢ trm_ctr J ∷ A ]

with jtyping : env type → trm → Prop :=
  | J_Tp : ∀ Γ M,
    T[ Γ ⊢ M ∷ ⊥ ] →
    J[ Γ ⊢ trm_app trm_tp M ]
  | J_Cont : ∀ Γ k A M,
    T[ Γ & (k ~ tp_cont A) ⊢ M ∷ A ] →
    J[ Γ & (k ~ tp_cont A) ⊢ trm_app (trm_fvar k) M ]

where "T[ Γ ⊢ M ∷ A ]" := (typing Γ M A)
  and "J[ Γ ⊢ J ]" := (jtyping Γ J).