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
  | twh_ctrl : ∀ J J',
    J →ₕⱼ J' →
    t_ctrl J →ₕₜ t_ctrl J'

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

Lemma twh_ctrl_cong {S : VSig} (J J' : jump (incK S)) :
  J ↠ₕⱼ J' →
  t_ctrl J ↠ₕₜ t_ctrl J'.
Proof. intro Hwh. cong Hwh. Qed.

Lemma jwh_jmp_cong {S : VSig} q (M M' : term S) :
  M ↠ₕₜ M' →
  j_jmp q M ↠ₕⱼ j_jmp q M'.
Proof. intro Hwh. cong Hwh. Qed.

(* ========================================================================== *)
(* Standard and internal reductions *)

Reserved Notation "M₁ '↠ₛₜ' M₂" (at level 50).
Reserved Notation "M₁ '↠ᵢₜ' M₂" (at level 50).
Reserved Notation "V₁ '↠ᵢᵥ' V₂" (at level 50).
Reserved Notation "J₁ '↠ₛⱼ' J₂" (at level 50).
Reserved Notation "J₁ '↠ᵢⱼ' J₂" (at level 50).

Inductive tstd {S : VSig} : term S → term S → Prop :=
  | tstdI : ∀ (M P N : term S),
    M ↠ₕₜ P →
    P ↠ᵢₜ N →
    M ↠ₛₜ N
with jstd {S : VSig} : jump S → jump S → Prop :=
  | jstdI : ∀ M P N,
    M ↠ₕⱼ P →
    P ↠ᵢⱼ N →
    M ↠ₛⱼ N

with tint {S : VSig} : term S → term S → Prop :=
  | tint_val : ∀ V V',
    V ↠ᵢᵥ V' →
    V ↠ᵢₜ V'
  | tint_app : ∀ M M' N N',
    M ↠ᵢₜ M' →
    N ↠ₛₜ N' →
    t_app M N ↠ᵢₜ t_app M' N'
  | tint_ctrl : ∀ J J',
    J ↠ₛⱼ J' →
    t_ctrl J ↠ᵢₜ t_ctrl J'
with vint {S : VSig} : value S → value S → Prop :=
  | vint_var : ∀ x,
    v_var x ↠ᵢᵥ v_var x
  | vint_lam : ∀ M N,
    M ↠ₛₜ N →
    v_lam M ↠ᵢᵥ v_lam N
with jint {S : VSig} : jump S → jump S → Prop :=
  | jint_jmp : ∀ q M M',
    M ↠ₛₜ M' →
    j_jmp q M ↠ᵢⱼ j_jmp q M'

where "M₁ ↠ₛₜ M₂" := (@tstd _ M₁ M₂)
  and "M₁ ↠ᵢₜ M₂" := (@tint _ M₁ M₂)
  and "V₁ ↠ᵢᵥ V₂" := (@vint _ V₁ V₂)
  and "J₁ ↠ₛⱼ J₂" := (@jstd _ J₁ J₂)
  and "J₁ ↠ᵢⱼ J₂" := (@jint _ J₁ J₂).

(* -------------------------------------------------------------------------- *)

Lemma tint_std {S : VSig} : ∀ (M M' : term S),
  M ↠ᵢₜ M' →
  M ↠ₛₜ M'.
Proof.
  intros M M' Htint.
  constructor 1 with (P := M).
  - apply twh_refl.
  - apply Htint.
Qed.
Lemma jint_std {S : VSig} : ∀ (J J' : jump S),
  J ↠ᵢⱼ J' →
  J ↠ₛⱼ J'.
Proof.
  intros J J' Hjint.
  constructor 1 with (P := J).
  - apply jwh_refl.
  - apply Hjint.
Qed.

Lemma tint_refl {S : VSig} : ∀ (M : term S),
  M ↠ᵢₜ M
 with vint_refl {S : VSig} : ∀ (V : value S),
  V ↠ᵢᵥ V
 with jint_refl {S : VSig} : ∀ (J : jump S),
  J ↠ᵢⱼ J.
Proof.
(* tint_refl *)
{
  intro M.
  induction M.
  + constructor. apply vint_refl.
  + constructor.
    - apply IHM1.
    - apply tint_std. apply IHM2.
  + constructor. apply jint_std. apply jint_refl.
}
(* vint_refl *)
{
  intro V.
  induction V.
  + constructor.
  + constructor. apply tint_std. apply tint_refl.
}
(* jint_refl *)
{
  intro J.
  induction J.
  constructor.
  apply tint_std. apply tint_refl.
}
Qed.

Lemma tstd_refl {S : VSig} (M : term S) :
  M ↠ₛₜ M.
Proof.
  econstructor.
  - apply twh_refl.
  - apply tint_refl.
Qed.
Lemma jstd_refl {S : VSig} (J : jump S) :
  J ↠ₛⱼ J.
Proof.
  econstructor.
  - apply jwh_refl.
  - apply jint_refl.
Qed.

Lemma twh_std {S : VSig} (M M' : term S) :
  M ↠ₕₜ M' →
  M ↠ₛₜ M'.
Proof.
  intro Hwh.
  econstructor.
  - apply Hwh.
  - apply tint_refl.
Qed.
Lemma jwh_std {S : VSig} (J J' : jump S) :
  J ↠ₕⱼ J' →
  J ↠ₛⱼ J'.
Proof.
  intro Hwh.
  econstructor.
  - apply Hwh.
  - apply jint_refl.
Qed.
Lemma twh_std' {S : VSig} (M M' : term S) :
  M →ₕₜ M' →
  M ↠ₛₜ M'.
Proof.
  intro Hwh. apply twh_std. constructor. apply Hwh.
Qed.
Lemma jwh_std' {S : VSig} (J J' : jump S) :
  J →ₕⱼ J' →
  J ↠ₛⱼ J'.
Proof.
  intro Hwh. apply jwh_std. constructor. apply Hwh.
Qed.

Lemma tstd_app_L_cong {S : VSig} (M M' N : term S) :
  M ↠ₛₜ M' →
  t_app M N ↠ₛₜ t_app M' N.
Proof.
  intro Hstd.
  destruct Hstd as [M P M' HMwhP HPintM'].
  econstructor.
  + apply twh_app_L_cong. apply HMwhP.
  + constructor.
    - apply HPintM'.
    - apply tstd_refl.
Qed.

Lemma tstd_app_R_cong {S : VSig} (M N N' : term S) :
  N ↠ₛₜ N' →
  t_app M N ↠ₛₜ t_app M N'.
Proof.
  intro Hstd.
  econstructor.
  + apply twh_refl.
  + constructor.
    - apply tint_refl.
    - apply Hstd.
Qed.

Lemma tstd_app {S : VSig} (M₁ M₂ N₁ N₂ : term S) :
  M₁ ↠ₛₜ M₂ →
  N₁ ↠ₛₜ N₂ →
  t_app M₁ N₁ ↠ₛₜ t_app M₂ N₂.
Proof.
  intros Hstd₁ Hstd₂.
  inversion Hstd₁ as [? P ? HM₁whP HPintM₂]; subst.
  econstructor.
  - apply twh_app_L_cong. apply HM₁whP.
  - constructor.
    * apply HPintM₂.
    * apply Hstd₂.
Qed.

Lemma tstd_ctrl_cong {S : VSig} (J J' : jump (incK S)) :
  J ↠ₛⱼ J' →
  t_ctrl J ↠ₛₜ t_ctrl J'.
Proof.
  intro Hstd.
  econstructor.
  + apply twh_refl.
  + constructor.
    apply Hstd.
Qed.

Lemma jstd_jmp_cong {S : VSig} q (M M' : term S) :
  M ↠ₛₜ M' →
  j_jmp q M ↠ₛⱼ j_jmp q M'.
Proof.
  intro Hstd.
  destruct Hstd as [M P M' HMwhP HPintM'].
  econstructor.
  + apply jwh_jmp_cong. apply HMwhP.
  + constructor.
    apply tint_std. apply HPintM'.
Qed.

Lemma tred_std {S : VSig} : ∀ (M N : term S),
  M →ₜ N →
  M ↠ₛₜ N
 with vred_int {S : VSig} : ∀ (V V' : value S),
  V →ᵥ V' →
  V ↠ᵢᵥ V'
 with jred_std {S : VSig} : ∀ (J J' : jump S),
  J →ⱼ J' →
  J ↠ₛⱼ J'.
Proof.
(* tred_std *)
{
  intros M N Hred.
  induction Hred;
    try (apply twh_std'; constructor; fail).
  + econstructor.
    - apply twh_refl.
    - constructor. apply vred_int. apply H.
  + apply tstd_app_L_cong.
    apply IHHred.
  + apply tstd_app_R_cong.
    apply IHHred.
  + apply tstd_ctrl_cong.
    apply jred_std.
    apply H.
}
(* vred_int *)
{
  intros V V' Hred.
  induction Hred.
  + constructor. apply tred_std. apply H.
}
(* jred_std *)
{
  intros J J' Hred.
  induction Hred.
  + apply jwh_std'. constructor.
  + apply jstd_jmp_cong.
    apply tred_std.
    apply H.
}
Qed.

(* ========================================================================== *)
(* fmap lemmas - the relations are preserved under fmap *)

(* -------------------------------------------------------------------------- *)
(* Weah head map lemma *)

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

Lemma twh_map' {S T : VSig} : ∀ (φ : prod_arr S T) M M',
  M →ₕₜ M' →
  fmap φ M ↠ₕₜ fmap φ M'
 with jwh_map' {S T : VSig} : ∀ (φ : prod_arr S T) J J',
  J →ₕⱼ J' →
  fmap φ J ↠ₕⱼ fmap φ J'.
Proof.
(* twh_map' *)
{
  intros φ M M' Hwh.
  induction Hwh.
  + term_simpl. constructor. constructor.
  + term_simpl. rewrite fmap_struct_subst with (E := e_appl e_hole N).
    term_simpl. constructor. constructor.
  + term_simpl. rewrite fmap_struct_subst with (E := e_appr V e_hole).
    term_simpl. constructor. constructor.
  + term_simpl. apply twh_app_L_cong. apply IHHwh.
  + term_simpl. apply twh_app_R_cong. apply IHHwh.
  + term_simpl. apply twh_ctrl_cong. apply jwh_map'. apply H.
}
(* jwh_map' *)
{
  intros φ J J' Hwh.
  induction Hwh.
  + term_simpl. destruct q.
    - econstructor 3.
      * apply jwh_jmp_cong.
        apply twh_ctrl_plug with (E := e_hole) (J := bind (φ ↑) J).
      * econstructor 3.
        ++ constructor. constructor.
        ++ rewrite subst_struct_subst.
           rewrite ecomp_pure.
           apply jwh_refl.
    - constructor. constructor.
  + term_simpl. destruct q.
    - apply jwh_jmp_cong.
      apply twh_map'. apply H.
    - apply jwh_jmp_cong.
      apply twh_map'. apply H.
}
Qed.

Lemma twh_map {S T : VSig} : ∀ (φ : prod_arr S T) M M',
  M ↠ₕₜ M' →
  fmap φ M ↠ₕₜ fmap φ M'.
Proof.
  intros φ M M' Hwh.
  induction Hwh as [ M₁ M₂ | M | M₁ M' M₂ ].
  + apply twh_map'. apply H.
  + apply twh_refl.
  + econstructor 3.
    - apply IHHwh1.
    - apply IHHwh2.
Qed.

Lemma jwh_map {S T : VSig} : ∀ (φ : prod_arr S T) J J',
  J ↠ₕⱼ J' →
  fmap φ J ↠ₕⱼ fmap φ J'.
Proof.
  intros φ J J' Hwh.
  induction Hwh as [ J₁ J₂ | J | J₁ J' J₂ ].
  + apply jwh_map'. apply H.
  + apply jwh_refl.
  + econstructor 3.
    - apply IHHwh1.
    - apply IHHwh2.
Qed.

(* -------------------------------------------------------------------------- *)
(* Standard and internal map lemmas *)

Lemma tint_map {S T : VSig} (φ : prod_arr S T) (M₁ M₂ : term S) :
  M₁ ↠ᵢₜ M₂ →
  fmap φ M₁ ↠ᵢₜ fmap φ M₂
 with vint_map {S T : VSig} (φ : prod_arr S T) (V₁ V₂ : value S) :
  V₁ ↠ᵢᵥ V₂ →
  fmap φ V₁ ↠ᵢᵥ fmap φ V₂
 with jint_map {S T : VSig} (φ : prod_arr S T) (J₁ J₂ : jump S) :
  J₁ ↠ᵢⱼ J₂ →
  fmap φ J₁ ↠ᵢⱼ fmap φ J₂

 with tstd_map {S T : VSig} (φ : prod_arr S T) (M₁ M₂ : term S) :
  M₁ ↠ₛₜ M₂ →
  fmap φ M₁ ↠ₛₜ fmap φ M₂
 with jstd_map {S T : VSig} (φ : prod_arr S T) (J₁ J₂ : jump S) :
  J₁ ↠ₛⱼ J₂ →
  fmap φ J₁ ↠ₛⱼ fmap φ J₂.
Proof.
(* tint_map *)
{
  intro Htint.
  induction Htint.
  + term_simpl. constructor. apply vint_map. apply H.
  + term_simpl. constructor.
    - apply IHHtint.
    - apply tstd_map. apply H.
  + term_simpl. constructor. apply jstd_map. apply H.
}
(* vint_map *)
{
  intros Hvint.
  induction Hvint.
  + term_simpl. apply vint_refl.
  + term_simpl. constructor. apply tstd_map. apply H.
}
(* jint_map *)
{
  intros Hjint.
  induction Hjint.
  + term_simpl.
    destruct q.
    - constructor.
      apply tstd_map. apply H.
    - constructor.
      apply tstd_map. apply H.
}
(* tstd_map *)
{
  intros Hstd.
  induction Hstd.
  + econstructor.
    - apply twh_map. apply H.
    - apply tint_map. apply H0.
}
(* jstd_map *)
{
  intros Hstd.
  induction Hstd.
  + econstructor.
    - apply jwh_map. apply H.
    - apply jint_map. apply H0.
}
Qed.

(* ========================================================================== *)
(* Bind lemmas - the relations are preserved under bind *)

(* -------------------------------------------------------------------------- *)
(* Weak head bind lemma *)

Lemma twh_plug {S : VSig} (M M' : term S) E :
  M ↠ₕₜ M' →
  eplug E M ↠ₕₜ eplug E M'.
Proof.
  intro Hwh.
  induction E.
  + apply Hwh.
  + term_simpl. apply twh_app_L_cong. apply IHE.
  + term_simpl. apply twh_app_R_cong. apply IHE.
Qed.

Lemma twh_bind' {S T : VSig} : ∀ (φ : S {→} T) M M',
  M →ₕₜ M' →
  bind φ M ↠ₕₜ bind φ M'
 with jwh_bind' {S T : VSig} : ∀ (φ : S {→} T) J J',
  J →ₕⱼ J' →
  bind φ J ↠ₕⱼ bind φ J'.
Proof.
(* twh_bind' *)
{
  intros φ M M' Hwh.
  induction Hwh.
  + term_simpl. constructor. constructor.
  + term_simpl. rewrite bind_struct_subst with (E := e_appl e_hole N).
    term_simpl. constructor. constructor.
  + term_simpl. rewrite bind_struct_subst with (E := e_appr V e_hole).
    term_simpl. constructor. constructor.
  + term_simpl. apply twh_app_L_cong. apply IHHwh.
  + term_simpl. apply twh_app_R_cong. apply IHHwh.
  + term_simpl. apply twh_ctrl_cong. apply jwh_bind'. apply H.
}
(* jwh_bind' *)
{
  intros φ J J' Hwh.
  induction Hwh.
  + term_simpl. destruct q.
    - destruct (sub_k φ k).
      econstructor 3.
      * apply jwh_jmp_cong.
        apply twh_ctrl_plug with (E := E) (J := bind (φ ↑) J).
      * econstructor 3.
        ++ constructor. constructor.
        ++ rewrite subst_struct_subst.
           rewrite ecomp_pure. simpl ecomp.
           apply jwh_refl.
    - constructor. constructor.
  + term_simpl. destruct q.
    - destruct (sub_k φ k).
      apply jwh_jmp_cong. apply twh_plug.
      apply twh_bind'. apply H.
    - apply jwh_jmp_cong.
      apply twh_bind'. apply H.
}
Qed.

Lemma twh_bind {S T : VSig} : ∀ (φ : S {→} T) M M',
  M ↠ₕₜ M' →
  bind φ M ↠ₕₜ bind φ M'.
Proof.
  intros φ M M' Hwh.
  induction Hwh.
  + apply twh_bind'. apply H.
  + apply twh_refl.
  + econstructor 3.
    - apply IHHwh1.
    - apply IHHwh2.
Qed.

Lemma jwh_bind {S T : VSig} : ∀ (φ : S {→} T) J J',
  J ↠ₕⱼ J' →
  bind φ J ↠ₕⱼ bind φ J'.
Proof.
  intros φ J J' Hwh.
  induction Hwh.
  + apply jwh_bind'. apply H.
  + apply jwh_refl.
  + econstructor 3.
    - apply IHHwh1.
    - apply IHHwh2.
Qed.

(* -------------------------------------------------------------------------- *)
(* Standard and internal bind lemmas *)
(* We use auxiliary definitions of standard reductions
    for evaluation contexts and substitutions *)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)
(* standard reduction of evaluation contexts *)

Reserved Notation "E₁ ↠ₛₑ E₂" (at level 50).

Inductive estd {S : VSig} : ectx S → ectx S → Prop :=
  | estd_hole :
    e_hole ↠ₛₑ e_hole
  | estd_appl : ∀ E₁ E₂ M₁ M₂,
    E₁ ↠ₛₑ E₂ →
    M₁ ↠ₛₜ M₂ →
    e_appl E₁ M₁ ↠ₛₑ e_appl E₂ M₂
  | estd_appr : ∀ V₁ V₂ E₁ E₂,
    V₁ ↠ᵢᵥ V₂ →
    E₁ ↠ₛₑ E₂ →
    e_appr V₁ E₁ ↠ₛₑ e_appr V₂ E₂

where "E₁ ↠ₛₑ E₂" := (@estd _ E₁ E₂).

Lemma estd_refl {S : VSig} (E : ectx S) :
  E ↠ₛₑ E.
Proof.
  induction E.
  + constructor.
  + constructor.
    - apply IHE.
    - apply tstd_refl.
  + constructor.
    - apply vint_refl.
    - apply IHE.
Qed.

Lemma estd_map {S T : VSig} (φ : prod_arr S T) (E₁ E₂ : ectx S) :
  E₁ ↠ₛₑ E₂ →
  fmap φ E₁ ↠ₛₑ fmap φ E₂.
Proof.
  intro Hestd.
  induction Hestd.
  + term_simpl. constructor.
  + term_simpl. constructor.
    - apply IHHestd.
    - apply tstd_map. apply H.
  + term_simpl. constructor.
    - apply vint_map. apply H.
    - apply IHHestd.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)
(* standard reduction of substitutions *)

Definition ssstd {S : VSig} (s₁ s₂ : ssub S) :=
  let (q₁, E₁) := s₁ in
  let (q₂, E₂) := s₂ in
  q₁ = q₂ ∧ E₁ ↠ₛₑ E₂.

Notation "s₁ ↠ₛₛₛ s₂" := (@ssstd _ s₁ s₂) (at level 50).

Lemma ssstd_refl {S : VSig} (s : ssub S) :
  s ↠ₛₛₛ s.
Proof.
  unfold ssstd.
  destruct s.
  split.
  + reflexivity.
  + apply estd_refl.
Qed.

Lemma ssstd_map {S T : VSig} (φ : prod_arr S T) (s₁ s₂ : ssub S) :
  s₁ ↠ₛₛₛ s₂ →
  fmap φ s₁ ↠ₛₛₛ fmap φ s₂.
Proof.
  intro Hssstd.
  unfold ssstd.
  destruct s₁ as [q₁ E₁].
  destruct s₂ as [q₂ E₂].
  term_simpl.
  split.
  + f_equal. apply Hssstd.
  + apply estd_map. apply Hssstd.
Qed.

Definition sstd {S T : VSig} (φ φ' : S {→} T) :=
  (∀ x, sub_v φ x ↠ᵢᵥ sub_v φ' x)
  ∧ (∀ k, sub_k φ k ↠ₛₛₛ sub_k φ' k).

Notation "φ₁ ↠ₛₛ φ₂" := (@sstd _ _ φ₁ φ₂) (at level 50).

Lemma sstd_refl {S T : VSig} (φ : S {→} T) :
  φ ↠ₛₛ φ.
Proof.
  constructor.
  + intro x. apply vint_refl.
  + intro k. apply ssstd_refl.
Qed.

Lemma sstd_vlift {S T : VSig} (φ φ' : S {→} T) :
  φ ↠ₛₛ φ' →
  φ ↑ᵥ ↠ₛₛ φ' ↑ᵥ.
Proof.
  intro Hsstd.
  constructor.
  + intro x. destruct x as [| x].
    - term_simpl. apply vint_refl.
    - term_simpl. apply vint_map. apply Hsstd.
  + intro k. apply ssstd_map. apply Hsstd.
Qed.

Lemma sstd_klift {S T : VSig} (φ φ' : S {→} T) :
  φ ↠ₛₛ φ' →
  φ ↑ₖ ↠ₛₛ φ' ↑ₖ.
Proof.
  intro Hsstd.
  constructor.
  + intro x. term_simpl.
    apply vint_map. apply Hsstd.
  + intro k. destruct k as [| k].
    - term_simpl. split.
      * reflexivity.
      * apply estd_hole.
    - term_simpl. apply ssstd_map. apply Hsstd.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)
(* Standard and internal bind lemmas *)

Lemma tstd_plug {S : VSig} : ∀ E E' (M M' : term S),
  E ↠ₛₑ E' →
  M ↠ₛₜ M' →
  eplug E M ↠ₛₜ eplug E' M'.
Proof.
  intros E E' M M' Hestd Hstd.
  induction Hestd.
  + term_simpl. apply Hstd.
  + term_simpl. inversion IHHestd as [? P ? HMwhP HPintM']; subst.
    econstructor.
    - apply twh_app_L_cong. apply HMwhP.
    - constructor.
      * apply HPintM'.
      * apply H.
  + term_simpl. inversion IHHestd as [? P ? HMwhP HPintM']; subst.
    econstructor.
    - apply twh_app_R_cong. apply HMwhP.
    - constructor.
      * constructor. apply H.
      * apply tint_std. apply HPintM'.
Qed.

Lemma tint_bind {S T : VSig} : ∀ (φ φ' : S {→} T) M M',
  φ ↠ₛₛ φ' →
  M ↠ᵢₜ M' →
  bind φ M ↠ᵢₜ bind φ' M'
 with vint_bind {S T : VSig} : ∀ (φ φ' : S {→} T) V V',
  φ ↠ₛₛ φ' →
  V ↠ᵢᵥ V' →
  vbind φ V ↠ᵢᵥ vbind φ' V'
 with jint_bind {S T : VSig} : ∀ (φ φ' : S {→} T) J J',
  φ ↠ₛₛ φ' →
  J ↠ᵢⱼ J' →
  bind φ J ↠ᵢⱼ bind φ' J'

 with tstd_bind {S T : VSig} : ∀ (φ φ' : S {→} T) M M',
  φ ↠ₛₛ φ' →
  M ↠ₛₜ M' →
  bind φ M ↠ₛₜ bind φ' M'
 with jstd_bind {S T : VSig} : ∀ (φ φ' : S {→} T) J J',
  φ ↠ₛₛ φ' →
  J ↠ₛⱼ J' →
  bind φ J ↠ₛⱼ bind φ' J'.
Proof.
(* tint_bind *)
{
  intros φ φ' M M' Hsstd Htint.
  induction Htint.
  + term_simpl. constructor. apply vint_bind; assumption.
  + term_simpl. constructor.
    - apply IHHtint. apply Hsstd.
    - apply tstd_bind; assumption.
  + term_simpl. constructor. apply jstd_bind.
    - apply sstd_klift. apply Hsstd.
    - apply H.
}
(* vint_bind *)
{
  intros φ φ' V V' Hsstd Hvint.
  induction Hvint.
  + term_simpl. apply Hsstd.
  + term_simpl. constructor. apply tstd_bind.
    - apply sstd_vlift. apply Hsstd.
    - apply H.
}
(* jint_bind *)
{
  intros φ φ' J J' Hsstd Hjint.
  induction Hjint.
  + term_simpl.
    destruct q.
    - pose proof Hsstd as [_ Hsstdₖ].
      specialize Hsstdₖ with k.
      unfold ssstd in Hsstdₖ.

      destruct (sub_k φ k) as [q E].
      destruct (sub_k φ' k) as [q' E'].

      destruct Hsstdₖ as [Hq HE].
      rewrite Hq.
      constructor. apply tstd_plug.
      * apply HE.
      * apply tstd_bind; assumption.
    - constructor.
      apply tstd_bind; assumption.
}
(* tstd_bind *)
{
  intros φ φ' M M' Hsstd Hstd.
  inversion Hstd as [? P ? HMwhP HPintM']; subst.
  econstructor.
  + apply twh_bind. apply HMwhP.
  + apply tint_bind; assumption.
}
(* jstd_bind *)
{
  intros φ φ' J J' Hsstd Hstd.
  inversion Hstd as [? P ? HJwhP HPintJ']; subst.
  econstructor.
  + apply jwh_bind. apply HJwhP.
  + apply jint_bind; assumption.
}
Qed.

Lemma struct_sub_sstd {S : VSig} (E₁ E₂ : ectx (incK S)) :
  E₁ ↠ₛₑ E₂ →
  struct_sub E₁ ↠ₛₛ struct_sub E₂.
Proof.
  intro Hestd.
  constructor.
  + intro x. term_simpl. apply vint_refl.
  + intro k. destruct k as [| k ].
    - term_simpl. split; [ reflexivity |].
      apply Hestd.
    - term_simpl. split; [ reflexivity | apply estd_refl ].
Qed.

Lemma mk_subst_sstd {S : VSig} (V₁ V₂ : value S) :
  V₁ ↠ᵢᵥ V₂ →
  mk_subst V₁ ↠ₛₛ mk_subst V₂.
Proof.
  intros Hvint.
  constructor.
  + intro x. destruct x as [| x].
    - term_simpl. apply Hvint.
    - term_simpl. apply vint_refl.
  + intro k. term_simpl.
    split; [ reflexivity | apply estd_refl ].
Qed.

(* ========================================================================== *)
(* standardisation lemma *)

(* -------------------------------------------------------------------------- *)
(* standard reduction can be prepended by a weak head reduction *)

Lemma twh_std_std {S : VSig} (M₁ M M₂ : term S) :
  M₁ ↠ₕₜ M  →
  M  ↠ₛₜ M₂ →
  M₁ ↠ₛₜ M₂.
Proof.
  intros Hwh Hstd.
  inversion Hstd as [? P ? HMwhP HPintM₂]; subst.
  econstructor.
  + econstructor 3.
    - apply Hwh.
    - apply HMwhP.
  + apply HPintM₂.
Qed.

Lemma jwh_std_std {S : VSig} (J₁ J J₂ : jump S) :
  J₁ ↠ₕⱼ J  →
  J  ↠ₛⱼ J₂ →
  J₁ ↠ₛⱼ J₂.
Proof.
  intros Hwh Hstd.
  inversion Hstd as [? P ? HJwhP HPintJ₂]; subst.
  econstructor.
  + econstructor 3.
    - apply Hwh.
    - apply HJwhP.
  + apply HPintJ₂.
Qed.

(* -------------------------------------------------------------------------- *)
(* ↠ᵢ∙↠ₕ ⊆ ↠ₛ - composites of the form ↠ᵢ∙↠ₕ can be standardised *)

Lemma tint_wh_std' {S : VSig} (M₁ M M₂ : term S) :
  M₁ ↠ᵢₜ M  →
  M  →ₕₜ M₂ →
  M₁ ↠ₛₜ M₂
 with jint_wh_std' {S : VSig} (J₁ J J₂ : jump S) :
  J₁ ↠ᵢⱼ J  →
  J  →ₕⱼ J₂ →
  J₁ ↠ₛⱼ J₂.
Proof.
(* tint_wh_std' *)
{
  intros Htint Hwh.
  induction Hwh.
  + inversion Htint; subst.
    inversion H2; subst.
    inversion H1; subst.
    inversion H3; subst.
    inversion H0; subst.

    eapply twh_std_std.
    - econstructor 3.
      * apply twh_app_R_cong. apply H.
      * constructor. constructor.
    - apply tstd_bind.
      * apply mk_subst_sstd.
        apply H7.
      * apply H4.
  + inversion Htint; subst.
    inversion H2; subst.
    econstructor.
    - constructor. constructor.
    - constructor.
      apply jstd_bind.
      * apply struct_sub_sstd.
        constructor; [ apply estd_refl |].
        apply tstd_map. apply H3.
      * apply H1.
  + inversion Htint; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H0; subst.

    econstructor.
    - econstructor 3.
      * apply twh_app_R_cong.
        apply H.
      * constructor. constructor.
    - constructor.
      apply jstd_bind.
      * apply struct_sub_sstd.
        constructor; [| apply estd_refl ].
        apply vint_map.
        apply H1.
      * apply H6.
  + inversion Htint; subst.
    apply IHHwh in H2.
    apply tstd_app.
    - apply H2.
    - apply H3.
  + inversion Htint; subst.
    inversion H3; subst.
    apply IHHwh in H0.
    apply tint_std.
    constructor.
    - apply H2.
    - eapply twh_std_std.
      * apply H.
      * apply H0.
  + inversion Htint; subst.
    apply tstd_ctrl_cong.

    inversion H2; subst.

    pose proof (jint_wh_std' _ _ _ _ H1 H) as H3.
    eapply jwh_std_std.
    - apply H0.
    - apply H3.
}
(* jint_wh_std' *)
{
  intros Hjint Hwh.
  induction Hwh.
  + inversion Hjint; subst.
    inversion H1; subst.
    inversion H0; subst.

    eapply jwh_std_std.
    - econstructor 3.
      * apply jwh_jmp_cong.
        apply H.
      * constructor. constructor.
    - apply jstd_bind.
      * apply sstd_refl.
      * apply H4.
  + inversion Hjint; subst.
    apply jstd_jmp_cong.
    destruct H2.
    pose proof (tint_wh_std' _ _ _ _ H1 H) as H3.
    destruct H3.
    econstructor.
    - econstructor 3.
      * apply H0.
      * apply H2.
    - apply H3.
}
Qed.

Lemma tint_wh_std {S : VSig} (M₁ M M₂ : term S) :
  M₁ ↠ᵢₜ M  →
  M  ↠ₕₜ M₂ →
  M₁ ↠ₛₜ M₂.
Proof.
  intros Htint Hwh.
  generalize dependent M₁.
  induction Hwh; intros M₁ Htint.
  + eapply tint_wh_std'.
    - apply Htint.
    - apply H.
  + apply tint_std. apply Htint.
  + apply IHHwh1 in Htint.
    destruct Htint.
    apply IHHwh2 in H0.
    eapply twh_std_std.
    - apply H.
    - apply H0.
Qed.

Lemma jint_wh_std {S : VSig} (J₁ J J₂ : jump S) :
  J₁ ↠ᵢⱼ J  →
  J  ↠ₕⱼ J₂ →
  J₁ ↠ₛⱼ J₂.
Proof.
  intros Hjint Hwh.
  generalize dependent J₁.
  induction Hwh; intros J₁ Hjint.
  + eapply jint_wh_std'.
    - apply Hjint.
    - apply H.
  + apply jint_std.
    apply Hjint.
  + apply IHHwh1 in Hjint.
    destruct Hjint.
    apply IHHwh2 in H0.
    eapply jwh_std_std.
    - apply H.
    - apply H0.
Qed.

(* -------------------------------------------------------------------------- *)
(* Standard and internal reductions are transitive *)

Lemma tint_trans {S : VSig} (M₁ M M₂ : term S) :
  M₁ ↠ᵢₜ M  →
  M  ↠ᵢₜ M₂ →
  M₁ ↠ᵢₜ M₂
 with vint_trans {S : VSig} (V₁ V V₂ : value S) :
  V₁ ↠ᵢᵥ V  →
  V  ↠ᵢᵥ V₂ →
  V₁ ↠ᵢᵥ V₂
 with jint_trans {S : VSig} (J₁ J J₂ : jump S) :
  J₁ ↠ᵢⱼ J  →
  J  ↠ᵢⱼ J₂ →
  J₁ ↠ᵢⱼ J₂

 with tstd_trans {S : VSig} (M₁ M M₂ : term S) :
  M₁ ↠ₛₜ M  →
  M  ↠ₛₜ M₂ →
  M₁ ↠ₛₜ M₂
 with jstd_trans {S : VSig} (J₁ J J₂ : jump S) :
  J₁ ↠ₛⱼ J  →
  J  ↠ₛⱼ J₂ →
  J₁ ↠ₛⱼ J₂.
Proof.
(* tint_trans *)
{
  intros Htint₁ Htint₂.
  induction Htint₂.
  + inversion Htint₁; subst.
    constructor.
    eapply vint_trans.
    - apply H2.
    - apply H.
  + inversion Htint₁; subst.
    constructor.
    - apply IHHtint₂.
      apply H3.
    - eapply tstd_trans.
      * apply H4.
      * apply H.
  + inversion Htint₁; subst.
    constructor.
    eapply jstd_trans.
    - apply H2.
    - apply H.
}
(* vint_trans *)
{
  intros Hvint₁ Hvint₂.
  induction Hvint₂.
  + inversion Hvint₁; subst.
    apply vint_refl.
  + inversion Hvint₁; subst.
    constructor.
    eapply tstd_trans.
    - apply H2.
    - apply H.
}
(* jint_trans *)
{
  intros Hjint₁ Hjint₂.
  induction Hjint₂.
  + inversion Hjint₁; subst.
    constructor.
    eapply tstd_trans.
    - apply H2.
    - apply H.
}
(* tstd_trans *)
{
  intros Hstd₁ Hstd₂.
  destruct Hstd₁, Hstd₂.
  pose proof (tint_wh_std _ _ _ H0 H1) as H3.
  inversion H3; subst.
  econstructor.
  + econstructor 3.
    - apply H.
    - apply H4.
  + eapply tint_trans.
    - apply H5.
    - apply H2.
}
(* jstd_trans *)
{
  intros Hstd₁ Hstd₂.
  destruct Hstd₁, Hstd₂.
  pose proof (jint_wh_std _ _ _ H0 H1) as H3.
  destruct H3.
  econstructor.
  + econstructor 3.
    - apply H.
    - apply H3.
  + eapply jint_trans.
    - apply H4.
    - apply H2.
}
Qed.

(* -------------------------------------------------------------------------- *)
(* Standardisation lemma *)

Lemma standardisation {S : VSig} : ∀ (M N : term S),
  M →*ₜ N →
  M ↠ₛₜ N.
Proof.
  intros M N Hreds.
  induction Hreds.
  + apply tred_std. apply H.
  + apply tstd_refl.
  + eapply tstd_trans.
    - apply IHHreds1.
    - apply IHHreds2.
Qed.