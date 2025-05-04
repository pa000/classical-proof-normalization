Require Import Utf8.
Require Import Syntax Semantics WeakHead.
Require Import Binding.Lib Binding.Product Binding.Set.
Require Import Relation_Operators.

(* ========================================================================== *)
(* Operational semantics of jumps *)

Reserved Notation "J₁ ↦ⱼ J₂" (at level 50).

Inductive jop {S : VSig} : jump S → jump S → Prop :=
  | jop_beta : ∀ q E M (V : value S),
    j_jmp q (eplug E (t_app (v_lam M) V)) ↦ⱼ j_jmp q (eplug E (subst M V))
  | jop_ctrl : ∀ q E J,
    j_jmp q (eplug E (t_ctrl J)) ↦ⱼ subst J (s_sub q E)

where "J₁ ↦ⱼ J₂" := (@jop _ J₁ J₂).

Notation jop_rtc J₁ J₂ := (clos_refl_trans _ jop J₁ J₂).
Notation "J₁ '↦↦ⱼ' J₂" := (jop_rtc J₁ J₂) (at level 50).

Lemma jop_jwh {S : VSig} (J₁ J₂ : jump S) :
  J₁ ↦ⱼ  J₂ →
  J₁ ↠ₕⱼ J₂.
Proof.
  intro Hop.
  induction Hop.
  - constructor. constructor.
    induction E; term_simpl.
    + constructor.
    + constructor. apply IHE.
    + constructor. apply IHE.
  - apply jwh_ctrl_plug.
Qed.
