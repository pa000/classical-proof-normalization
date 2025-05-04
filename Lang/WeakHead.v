Require Import Utf8.
Require Import Syntax Semantics.
Require Import Binding.Lib Binding.Product Binding.Set.
Require Import Relation_Operators.

(* ========================================================================== *)
(* Weak head reduction *)

Reserved Notation "M₁ '→ₕₜ' M₂" (at level 50).
Reserved Notation "J₁ '→ₕⱼ' J₂" (at level 50).

Inductive twh {S : VSig} : term S → term S → Prop :=
  | twh_beta : ∀ M (V : value S),
    t_app (v_lam M) V →ₕₜ subst M V
  | twh_C_L : ∀ (J : jump (incK S)) (N : term S),
    t_app (t_ctrl J) N →ₕₜ t_ctrl (struct_subst J (e_appl e_hole (shift N)))
  | twh_C_R : ∀ J (V : value S),
    t_app V (t_ctrl J) →ₕₜ t_ctrl (struct_subst J (e_appr (shift V) e_hole))

  | twh_app_L : ∀ M M' N,
    M →ₕₜ M' →
    t_app M N →ₕₜ t_app M' N
  | twh_app_R : ∀ (V : value S) N N',
    N →ₕₜ N' →
    t_app V N →ₕₜ t_app V N'

with jwh {S : VSig} : jump S → jump S → Prop :=
  | jwh_C_idem : ∀ (q : katom S) (J : jump (incK S)),
    j_jmp q (t_ctrl J) →ₕⱼ subst J (s_sub q e_hole)

  | jwh_jmp : ∀ q M M',
    M →ₕₜ M' →
    j_jmp q M →ₕⱼ j_jmp q M'

where "M₁ →ₕₜ M₂" := (@twh _ M₁ M₂)
  and "J₁ →ₕⱼ J₂" := (@jwh _ J₁ J₂).

Notation jwh_rtc J₁ J₂ := (clos_refl_trans _ jwh J₁ J₂).
Notation "J₁ '↠ₕⱼ' J₂" := (jwh_rtc J₁ J₂) (at level 50).

Notation twh_rtc M₁ M₂ := (clos_refl_trans _ twh M₁ M₂).
Notation "M₁ '↠ₕₜ' M₂" := (twh_rtc M₁ M₂) (at level 50).

(* -------------------------------------------------------------------------- *)

Lemma twh_refl {S : VSig} (M : term S) :
  M ↠ₕₜ M.
Proof. constructor 2. Qed.
Lemma jwh_refl {S : VSig} (J : jump S) :
  J ↠ₕⱼ J.
Proof. constructor 2. Qed.

Lemma twh_app_L_cong {S : VSig} (M M' N : term S) :
  M ↠ₕₜ M' →
  t_app M N ↠ₕₜ t_app M' N.
Proof. intro Hwh. cong Hwh. Qed.

Lemma twh_app_R_cong {S : VSig} (V : value S) (N N' : term S) :
  N ↠ₕₜ N' →
  t_app V N ↠ₕₜ t_app V N'.
Proof. intro Hwh. cong Hwh. Qed.

Lemma jwh_jmp_cong {S : VSig} q (M M' : term S) :
  M ↠ₕₜ M' →
  j_jmp q M ↠ₕⱼ j_jmp q M'.
Proof. intro Hwh. cong Hwh. Qed.

Lemma twh_ctrl_plug {S : VSig} (J : jump (incK S)) E :
  eplug E (t_ctrl J) ↠ₕₜ t_ctrl (struct_subst J (shift E)).
Proof.
  induction E.
  + term_simpl. rewrite struct_subst_pure. apply twh_refl.
  + term_simpl. econstructor 3.
    { apply twh_app_L_cong.
      apply IHE. }
    econstructor 3.
    { constructor. constructor. }
    rewrite struct_subst_comp with (E₂ := e_appl e_hole M).
    term_simpl. constructor 2.
  + term_simpl. econstructor 3.
    { apply twh_app_R_cong.
      apply IHE. }
    econstructor 3.
    { constructor. constructor. }
    rewrite struct_subst_comp with (E₂ := e_appr V e_hole).
    term_simpl. constructor 2.
Qed.

Lemma jwh_ctrl_plug {S : VSig} q (J : jump (incK S)) E :
  j_jmp q (eplug E (t_ctrl J)) ↠ₕⱼ subst J (s_sub q E).
Proof.
  econstructor 3.
  { apply jwh_jmp_cong. apply twh_ctrl_plug. }
  econstructor 3.
  { constructor. constructor. }
  rewrite subst_struct_subst. simpl.
  constructor 2.
Qed.

(* -------------------------------------------------------------------------- *)
(* alternative definition of jwh *)

Inductive bcred {S : VSig} : term S → term S → Prop :=
  | bcred_beta : ∀ M (V : value S),
    bcred (t_app (v_lam M) V) (subst M V)
  | bcred_C_L : ∀ (J : jump (incK S)) (N : term S),
    bcred (t_app (t_ctrl J) N) (t_ctrl (struct_subst J (e_appl e_hole (shift N))))
  | bcred_C_R : ∀ J (V : value S),
    bcred (t_app V (t_ctrl J)) (t_ctrl (struct_subst J (e_appr (shift V) e_hole))).

Notation "M₁ 'bcred*' M₂" := (clos_refl_trans _ bcred M₁ M₂) (at level 50).

Reserved Notation "J₁ '→ₕⱼ'' J₂" (at level 50).

Inductive jwh' {S : VSig} : jump S → jump S → Prop :=
  | jwh_plug : ∀ q E M N,
    bcred M N →
    j_jmp q (eplug E M) →ₕⱼ' j_jmp q (eplug E N)
  | jwh_idem : ∀ q J,
    j_jmp q (t_ctrl J) →ₕⱼ' subst J (s_sub q e_hole)

where "J₁ →ₕⱼ' J₂" := (@jwh' _ J₁ J₂).

Notation jwh'_rtc J₁ J₂ := (clos_refl_trans _ jwh' J₁ J₂).
Notation "J₁ '↠ₕⱼ'' J₂" := (jwh'_rtc J₁ J₂) (at level 50).

Lemma twh_bcred {S : VSig} (M M' : term S) :
  M →ₕₜ M' →
  ∃ E N N',
    M = eplug E N
    ∧ M' = eplug E N'
    ∧ bcred N N'.
Proof.
  intro Hwh.
  induction Hwh.
  - exists e_hole. repeat eexists. constructor.
  - exists e_hole. repeat eexists. constructor.
  - exists e_hole. repeat eexists. constructor.
  - destruct IHHwh as [E [P [P' [? [? ?]]]]]. subst.
    exists (e_appl E N). repeat eexists. assumption.
  - destruct IHHwh as [E [P [P' [? [? ?]]]]]. subst.
    exists (e_appr V E). repeat eexists. assumption.
Qed.

Lemma bcred_twh {S : VSig} E (M M' : term S) :
  bcred M M' →
  eplug E M →ₕₜ eplug E M'.
Proof.
  intro Hbcred.
  induction E; term_simpl.
  - destruct Hbcred; constructor.
  - constructor. apply IHE.
  - constructor. apply IHE.
Qed.

Lemma jwh_jwh' {S : VSig} (J J' : jump S) :
  J →ₕⱼ  J' →
  J →ₕⱼ' J'.
Proof.
  intro Hwh.
  induction Hwh.
  - constructor.
  - apply twh_bcred in H.
    destruct H as [E [N [N' [? [? ?]]]]]; subst.
    constructor. apply H1.
Qed.

Lemma jwh'_jwh {S : VSig} (J J' : jump S) :
  J →ₕⱼ' J' →
  J →ₕⱼ  J'.
Proof.
  intro Hwh.
  destruct Hwh.
  - induction E; term_simpl.
    + constructor. destruct H; constructor.
    + constructor. constructor.
      apply bcred_twh.
      apply H.
    + constructor. constructor.
      apply bcred_twh.
      apply H.
  - constructor.
Qed.

