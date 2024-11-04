Require Import Utf8.
Require Import Syntax.
Require Import Typing.
Require Import Binding.Lib Binding.Env Binding.Product.

Open Scope bind_scope.

Reserved Notation "M '→ₜ' M'" (at level 67).
Reserved Notation "J '→ⱼ' J'" (at level 67).
Reserved Notation "V '→ᵥ' V'" (at level 67).

Inductive tred {A : VSig} : term A → term A → Prop :=
  | tred_beta : ∀ M (V : value A),
    t_app (v_lam M) V →ₜ subst M V
  | tred_C_L : ∀ (J : jump (incK A)) (N : term A),
    t_app (t_ctrl J) N →ₜ t_ctrl (struct_subst J (e_appl e_hole (shift N)))
  | tred_C_R : ∀ J (V : value A),
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

with jred {A : VSig} : jump A → jump A → Prop :=
  | jred_idem : ∀ (q : katom (kv A)) (J : jump (incK A)),
    j_jmp q (t_ctrl J) →ⱼ subst J (s_sub q e_hole)

  | jred_jmp : ∀ q M M',
    M →ₜ M' →
    j_jmp q M →ⱼ j_jmp q M'

with vred {A : VSig} : value A → value A → Prop :=
  | vred_lam : ∀ M M',
    M →ₜ M' →
    v_lam M →ᵥ v_lam M'

where "M →ₜ M'" := (tred M M')
  and "J →ⱼ J'" := (jred J J')
  and "V →ᵥ V'" := (vred V V').
