Require Import Utf8.
Require Import Syntax.
Require Import Typing.
Require Import Binding.Lib Binding.Env Binding.Product Binding.Set.
Require Import Relation_Operators.

Open Scope bind_scope.

Reserved Notation "M '→ₜ' M'" (at level 67).
Reserved Notation "J '→ⱼ' J'" (at level 67).
Reserved Notation "V '→ᵥ' V'" (at level 67).
Reserved Notation "E '→ₑ' E'" (at level 67).

Inductive tred {S : VSig} : term S → term S → Prop :=
  | tred_beta : ∀ M (V : value S),
    t_app (v_lam M) V →ₜ subst M V
  | tred_C_L : ∀ (J : jump (incK S)) (N : term S),
    t_app (t_ctrl J) N →ₜ t_ctrl (struct_subst J (e_appl e_hole (shift N)))
  | tred_C_R : ∀ J (V : value S),
    t_app V (t_ctrl J) →ₜ t_ctrl (struct_subst J (e_appr (shift V) e_hole))

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

Notation tred_tc M₁ M₂ := (clos_trans_1n _ tred M₁ M₂).
Notation vred_tc V₁ V₂ := (clos_trans_1n _ vred V₁ V₂).
Notation jred_tc J₁ J₂ := (clos_trans_1n _ jred J₁ J₂).

Notation "M →+ₜ M'" := (tred_tc M M') (at level 100).
Notation "J →+ⱼ J'" := (jred_tc J J') (at level 100).
Notation "V →+ᵥ V'" := (vred_tc V V') (at level 100).

Notation tred_rtc M₁ M₂ := (clos_refl_trans _ tred M₁ M₂).
Notation vred_rtc V₁ V₂ := (clos_refl_trans _ vred V₁ V₂).
Notation jred_rtc J₁ J₂ := (clos_refl_trans _ jred J₁ J₂).

Notation "M '→*ₜ' M'" := (tred_rtc M M') (at level 50).
Notation "J '→*ⱼ' J'" := (jred_rtc J J') (at level 50).
Notation "V '→*ᵥ' V'" := (vred_rtc V V') (at level 50).

(* -------------------------------------------------------------------------- *)
(* → and →* are preserved under fmap. *)

Ltac cong H :=
  induction H; [
    constructor; constructor; assumption
  | constructor 2
  | econstructor 3; [
      eassumption
    | assumption ]
  ].

Lemma tred_value_cong {S : VSig} : ∀ (V V' : value S),
  V →*ᵥ V' →
  V →*ₜ V'.
Proof.
  intros V V' Hreds.
  cong Hreds.
Qed.

Lemma tred_appl_cong {S : VSig} : ∀ (M M' N : term S),
  M →*ₜ M' →
  t_app M N →*ₜ t_app M' N.
Proof.
  intros M M' N Hreds.
  cong Hreds.
Qed.

Lemma tred_appr_cong {S : VSig} : ∀ (M N N' : term S),
  N →*ₜ N' →
  t_app M N →*ₜ t_app M N'.
Proof.
  intros M M' N Hreds.
  cong Hreds.
Qed.

Lemma tred_ctrl_cong {S : VSig} : ∀ (J J' : jump (incK S)),
  J →*ⱼ J' →
  t_ctrl J →*ₜ t_ctrl J'.
Proof.
  intros J J' Hreds.
  cong Hreds.
Qed.

Lemma tred_plug {S : VSig} : ∀ (E : ectx S) (M M' : term S),
  M →ₜ M' →
  eplug E M →ₜ eplug E M'.
Proof.
  intros E M M' Hred.
  induction E.
  + term_simpl. apply Hred.
  + term_simpl. constructor. apply IHE.
  + term_simpl. constructor. apply IHE.
Qed.

Lemma tred_plug_cong {S : VSig} : ∀ (E : ectx S) (M M' : term S),
  M →*ₜ M' →
  eplug E M →*ₜ eplug E M'.
Proof.
  intros E M M' Hreds.
  induction Hreds.
  + constructor. term_simpl.
    apply tred_plug. apply H.
  + constructor 2.
  + constructor 3 with (y := eplug E y).
    apply IHHreds1.
    apply IHHreds2.
Qed.

Lemma vred_lam_cong {S : VSig} : ∀ (M M' : term (incV S)),
  M →*ₜ M' →
  v_lam M →*ᵥ v_lam M'.
Proof.
  intros M M' Hreds.
  cong Hreds.
Qed.

Lemma jred_jmp_cong {S : VSig} : ∀ (M M' : term S) q,
  M →*ₜ M' →
  j_jmp q M →*ⱼ j_jmp q M'.
Proof.
  intros M M' q Hreds.
  cong Hreds.
Qed.

Lemma struct_subst_fmap {S T : VSig} (E : ectx S) (φ : prod_arr S T) :
  struct_sub (shift (fmap φ E)) ∘ (φ ↑) ̂ ≡ (φ ↑) ̂ ∘ struct_sub (shift E).
Proof.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. destruct k.
    - term_simpl.
      rewrite <- map_to_bind.
      term_simpl.
      rewrite ecomp_pure.
      reflexivity.
    - term_simpl. reflexivity.
Qed.

Lemma tred_map {S T : VSig} : ∀ (M M' : term S) (φ : prod_arr S T),
  M →ₜ M' →
  fmap φ M →ₜ fmap φ M'
with vred_map {S T : VSig} : ∀ (V V' : value S) (φ : prod_arr S T),
  V →ᵥ V' →
  fmap φ V →ᵥ fmap φ V'
with jred_map {S T : VSig} : ∀ (J J' : jump S) (φ : prod_arr S T),
  J →ⱼ J' →
  fmap φ J →ⱼ fmap φ J'.
Proof.
(* tred_map *)
{
  intros M M' φ Hred.
  induction Hred.
  + term_simpl.
    constructor.
  + term_simpl.
    unfold struct_subst.
    erewrite <- bind_map_comm.
    - apply tred_C_L.
    - replace (e_appl e_hole (shift (fmap φ N))) with (shift (fmap φ (e_appl e_hole N))) by reflexivity.
      replace (e_appl e_hole (shift N)) with (shift (e_appl e_hole N)) by reflexivity.
      apply struct_subst_fmap.
  + term_simpl.
    unfold struct_subst.
    erewrite <- bind_map_comm.
    - apply tred_C_R.
    - replace (e_appr (shift (fmap φ V)) e_hole) with (shift (fmap φ (e_appr V e_hole))) by reflexivity.
      replace (e_appr (shift V) e_hole) with (shift (e_appr V e_hole)) by reflexivity.
      apply struct_subst_fmap.
  + term_simpl. constructor. apply vred_map. apply H.
  + term_simpl. constructor. apply IHHred.
  + term_simpl. constructor. apply IHHred.
  + term_simpl. constructor. apply jred_map. apply H.
}
(* vred_map *)
{
  intros V V' φ Hred.
  induction Hred.
  + term_simpl. constructor. apply tred_map. apply H.
}
(* jred_map *)
{
  intros J J' φ Hred.
  induction Hred.
  + term_simpl. constructor.
  + term_simpl. constructor. apply tred_map. apply H.
}
Qed.

Lemma treds_map {S T : VSig} : ∀ (M M' : term S) (φ : prod_arr S T),
  M →*ₜ M' →
  fmap φ M →*ₜ fmap φ M'
with vreds_map {S T : VSig} : ∀ (V V' : value S) (φ : prod_arr S T),
  V →*ᵥ V' →
  fmap φ V →*ᵥ fmap φ V'
with jreds_map {S T : VSig} : ∀ (J J' : jump S) (φ : prod_arr S T),
  J →*ⱼ J' →
  fmap φ J →*ⱼ fmap φ J'.
Proof.
(* treds_map *)
{
  intros M M' φ Hreds.
  induction Hreds.
  + constructor. apply tred_map. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
(* vreds_map *)
{
  intros M M' φ Hreds.
  induction Hreds.
  + constructor. apply vred_map. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
(* jreds_map *)
{
  intros M M' φ Hreds.
  induction Hreds.
  + constructor. apply jred_map. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
Qed.

(* -------------------------------------------------------------------------- *)
Lemma treds_ctrl_plug {S : VSig} (J : jump (incK S)) E :
  eplug E (t_ctrl J) →*ₜ t_ctrl (struct_subst J (shift E)).
Proof.
  induction E as [| E IHE M | V E IHE ].
  + term_simpl. rewrite struct_subst_pure. constructor 2.
  + term_simpl. econstructor 3.
    { apply tred_appl_cong.
      apply IHE. }
    econstructor 3.
    { constructor. constructor. }
    rewrite struct_subst_comp with (E₂ := e_appl e_hole M).
    term_simpl. constructor 2.
  + term_simpl. econstructor 3.
    { apply tred_appr_cong.
      apply IHE. }
    econstructor 3.
    { constructor. constructor. }
    rewrite struct_subst_comp with (E₂ := e_appr V e_hole).
    term_simpl. constructor 2.
Qed.

