Require Import Utf8.
Require Import Binding.Lib Binding.Product Binding.Env.
Require Import Syntax.

Local Open Scope bind_scope.

Inductive ttype :=
  | tp_bottom : ttype
  | tp_arrow  : ttype → ttype → ttype.
Inductive ktype :=
  (* type of a continuation (A → ⊥⊥) *)
  | tp_cont   : ttype → ktype.

Definition envV A := A → ttype.
Definition envK A := A → ktype.

(* We use two environments:
   Δ for continuation variables and Γ for term variables *)
Reserved Notation "'T[' Δ ';' Γ '⊢' M '∷' A ']'".
Reserved Notation "'J[' Δ ';' Γ '⊢' J '∷' '⊥⊥' ']'".

Inductive ttyping {V K : Set} (Δ : envK K) (Γ : envV V) : term ⟨V, K⟩ → ttype → Prop :=
  | T_Var : ∀ x,
    T[ Δ; Γ ⊢ v_var x ∷ Γ x ]

  | T_App : ∀ M N A B,
    T[ Δ; Γ ⊢ M ∷ tp_arrow A B ] →
    T[ Δ; Γ ⊢ N ∷ A ] →
    (* --------------------*)
    T[ Δ; Γ ⊢ t_app M N ∷ B ]

  | T_Abs : ∀ M A B,
    T[ Δ; Γ▹A ⊢ M ∷ B ] →
    (* ---------------------------- *)
    T[ Δ; Γ ⊢ v_lam M ∷ tp_arrow A B ]

  | T_Ctrl : ∀ J A,
    J[ Δ▹tp_cont A; Γ ⊢ J ∷ ⊥⊥ ] →
    (* ------------------ *)
    T[ Δ; Γ ⊢ t_ctrl J ∷ A ]

with jtyping {V K : Set} (Δ : envK K) (Γ : envV V) : jump ⟨V, K⟩ → Prop :=
  | J_Tp : ∀ M,
    T[ Δ; Γ ⊢ M ∷ tp_bottom ] →
    (* ----------------------- *)
    J[ Δ; Γ ⊢ j_jmp k_tp M ∷ ⊥⊥ ]

  | J_Cont : ∀ M A k,
    Δ k = tp_cont A →
    T[ Δ; Γ ⊢ M ∷ A ] →
    (* ---------------------------- *)
    J[ Δ; Γ ⊢ j_jmp (k_var k) M ∷ ⊥⊥ ]

where "T[ Δ ; Γ ⊢ M ∷ A ]"  := (@ttyping _ _ Δ Γ M A)
  and "J[ Δ ; Γ ⊢ J ∷ ⊥⊥ ]" := (@jtyping _ _ Δ Γ J).