Require Import Utf8.
Require Import Syntax.
Require Import Typing.
Require Import Binding.Lib Binding.Env Binding.Product.
Require Import Relation_Operators.

Open Scope bind_scope.

Reserved Notation "M '→ₜ' M'" (at level 67).
Reserved Notation "J '→ⱼ' J'" (at level 67).
Reserved Notation "V '→ᵥ' V'" (at level 67).

Inductive tred {S : VSig} : term S → term S → Prop :=
  | tred_beta : ∀ M (V : value S),
    t_app (v_lam M) V →ₜ subst M V
  | tred_C_L : ∀ (J : jump (incK S)) (N : term S),
    t_app (t_ctrl J) N →ₜ t_ctrl (struct_subst J (e_appl e_hole (shift N)))
  | tred_C_R : ∀ J (V : value S),
    t_app V (t_ctrl J) →ₜ t_ctrl (struct_subst J (e_appr (shift V) e_hole))
  | tred_C_elim : ∀ M,
    t_ctrl (j_jmp (k_var VZ) (shift M)) →ₜ M

  | tred_value : ∀ V V',
    V →ᵥ V' →
    V →ₜ V'
  | tred_app_L : ∀ M M' N,
    M →ₜ M' →
    t_app M N →ₜ t_app M' N
  | tred_app_R : ∀ M N N',
    N →ₜ N' →
    t_app M N →ₜ t_app M N'
  | tred_ctrl : ∀ J J',
    J →ⱼ J' →
    t_ctrl J →ₜ t_ctrl J'

with jred {S : VSig} : jump S → jump S → Prop :=
  | jred_C_idem : ∀ (q : katom S) (J : jump (incK S)),
    j_jmp q (t_ctrl J) →ⱼ subst J (s_sub q e_hole)

  | jred_jmp : ∀ q M M',
    M →ₜ M' →
    j_jmp q M →ⱼ j_jmp q M'

with vred {S : VSig} : value S → value S → Prop :=
  | vred_lam : ∀ M M',
    M →ₜ M' →
    v_lam M →ᵥ v_lam M'

where "M →ₜ M'" := (tred M M')
  and "J →ⱼ J'" := (jred J J')
  and "V →ᵥ V'" := (vred V V').

Notation tred_rtc M₁ M₂ := (clos_trans_1n _ tred M₁ M₂).
Notation vred_rtc V₁ V₂ := (clos_trans_1n _ vred V₁ V₂).
Notation jred_rtc J₁ J₂ := (clos_trans_1n _ jred J₁ J₂).

Notation "M →+ₜ M'" := (tred_rtc M M') (at level 100).
Notation "J →+ⱼ J'" := (jred_rtc J J') (at level 100).
Notation "V →+ᵥ V'" := (vred_rtc V V') (at level 100).
