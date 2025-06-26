Require Import Utf8.
Require Import Syntax Semantics Typing.
Require Import Binding.Lib Binding.Set Binding.Product.

(* ========================================================================== *)
(* Normal forms *)

Inductive tnf {S : VSig} : term S → Prop :=
  | tnf_val : ∀ (V : value S),
    vnf V →
    tnf V
  | tnf_app_var : ∀ x M,
    (∀ J, M ≠ t_ctrl J) →
    tnf M →
    tnf (t_app (v_var x) M)
  | tnf_app_lam : ∀ M N₁ N₂,
    tnf (t_app N₁ N₂) →
    tnf (v_lam M) →
    tnf (t_app (v_lam M) (t_app N₁ N₂))
  | tnf_app_app : ∀ M₁ M₂ N,
    tnf (t_app M₁ M₂) →
    tnf N →
    tnf (t_app (t_app M₁ M₂) N)
  | tnf_ctrl : ∀ J,
    jnf J →
    tnf (t_ctrl J)

with vnf {S : VSig} : value S → Prop :=
  | vnf_var : ∀ x,
    vnf (v_var x)
  | vnf_lam : ∀ M,
    tnf M →
    vnf (v_lam M)

with jnf {S : VSig} : jump S → Prop :=
  | jnf_jmp_val : ∀ q M,
    (∀ J, M ≠ t_ctrl J) →
    tnf M →
    jnf (j_jmp q M).

Definition twn {S : VSig} (M : term S) := ∃ M', tnf M' ∧ M →*ₜ M'.
Definition jwn {S : VSig} (J : jump S) := ∃ J', jnf J' ∧ J →*ⱼ J'.

Lemma tnf_correct1 {S : VSig} (M : term S) :
  tnf M →
  ∀ M', ¬ (M →ₜ M')
 with vnf_correct1 {S : VSig} (V : value S) :
  vnf V →
  ∀ V', ¬ (V →ᵥ V')
 with jnf_correct1 {S : VSig} (J : jump S) :
  jnf J →
  ∀ J', ¬ (J →ⱼ J').
Proof.
(* tnf_correct1 *)
{
  intro Hnf.
  induction Hnf; intros M' Hred.
  - inversion Hred; subst.
    refine (vnf_correct1 _ _ _ _ H1).
    apply H.
  - inversion Hred; subst.
    + destruct (H J). reflexivity.
    + inversion H3; subst.
      inversion H1; subst.
    + destruct (IHHnf _ H3).
  - inversion Hred; subst.
    + apply (IHHnf2 _ H2).
    + apply (IHHnf1 _ H2).
  - inversion Hred; subst.
    + apply (IHHnf1 _ H2).
    + apply (IHHnf2 _ H2).
  - inversion Hred; subst.
    refine (jnf_correct1 _ _ _ _ H1).
    apply H.
}
(* vnf_correct1 *)
{
  intro Hnf.
  induction Hnf; intros V' Hred.
  - inversion Hred.
  - inversion Hred; subst.
    refine (tnf_correct1 _ _ _ _ H1).
    apply H.
}
(* jnf_correct1 *)
{
  intro Hnf.
  induction Hnf; intros J' Hred.
  inversion Hred; subst.
  - destruct (H J). reflexivity.
  - refine (tnf_correct1 _ _ _ _ H4).
    apply H0.
}
Qed.

Lemma tnf_correct2 {S : VSig} (M : term S) :
  (∀ M', ¬ (M →ₜ M')) → tnf M
 with vnf_correct2 {S : VSig} (V : value S) :
  (∀ V', ¬ (V →ᵥ V')) → vnf V
 with jnf_correct2 {S : VSig} (J : jump S) :
  (∀ J', ¬ (J →ⱼ J')) → jnf J.
Proof.
(* tnf_correct2 *)
{
  intro Hred.
  induction M.
  - constructor.
    apply vnf_correct2.
    intros V' Hredᵥ.
    apply tred_value in Hredᵥ.
    apply (Hred _ Hredᵥ).
  - destruct M1.
    + destruct V.
      * constructor.
        -- intros J HM2; subst.
          edestruct Hred. constructor.
        -- apply IHM2. intros M' HM'.
          apply tred_app_R with (M := v_var x) in HM'.
          destruct (Hred _ HM').
      * destruct M2.
        -- edestruct Hred. constructor.
        -- constructor.
          ++ apply IHM2. intros M' HM'.
            edestruct Hred.
            apply tred_app_R. apply HM'.
          ++ apply IHM1. intros M' HM'.
            edestruct Hred.
            apply tred_app_L. apply HM'.
        -- edestruct Hred. constructor.
    + constructor.
      * apply IHM1. intros M' HM'.
        edestruct Hred.
        apply tred_app_L. apply HM'.
      * apply IHM2. intros M' HM'.
        edestruct Hred.
        apply tred_app_R. apply HM'.
    + edestruct Hred. constructor.
  - constructor. apply jnf_correct2.
    intros J' HJ'.
    edestruct Hred.
    constructor. apply HJ'.
}
(* vnf_correct2 *)
{
  intros Hred.
  induction V.
  - constructor.
  - constructor. apply tnf_correct2.
    intros M' HM'.
    edestruct Hred.
    constructor. apply HM'.
}
(* jnf_correct2 *)
{
  intros Hred.
  induction J.
  pose proof (tnf_correct2 _ M) as IHM.
  destruct M.
  - constructor.
    + discriminate.
    + apply IHM.
      intros V' HV'.
      edestruct Hred.
      constructor. apply HV'.
  - constructor.
    + discriminate.
    + apply IHM.
      intros M' HM'.
      edestruct Hred.
      constructor. apply HM'.
  - edestruct Hred.
    constructor.
}
Qed.

Lemma twn_red {S : VSig} (M₁ M₂ : term S) :
  M₁ →ₜ M₂ →
  twn M₂ →
  twn M₁.
Proof.
  intros Hred Hwn.
  destruct Hwn as [N [Hnf Hred']].
  exists N. split.
  - apply Hnf.
  - econstructor 3.
    + constructor. apply Hred.
    + apply Hred'.
Qed.

Lemma twn_plug_ctrl {S : VSig} E (J : jump (incK S)) :
  jwn (struct_subst J (shift E)) →
  twn (eplug E (t_ctrl J)).
Proof.
  intro Hjwn.
  unfold jwn in Hjwn.
  destruct Hjwn as [J' [Hjnf Hjred]].
  exists (t_ctrl J'). split.
  - constructor. apply Hjnf.
  - econstructor 3.
    + apply treds_ctrl_plug.
    + apply tred_ctrl_cong. apply Hjred.
Qed.

Lemma twn_jwn {S : VSig} q (M : term S) :
  twn M →
  jwn (j_jmp q M).
Proof.
  intro Htwn.
  unfold twn in Htwn.
  destruct Htwn as [M' [Hnf HM]].
  destruct M'.
  - exists (j_jmp q V). split.
    + constructor.
      * discriminate.
      * apply Hnf.
    + apply jred_jmp_cong. apply HM.
  - exists (j_jmp q (t_app M'1 M'2)). split.
    + constructor.
      * discriminate.
      * apply Hnf.
    + apply jred_jmp_cong. apply HM.
  - inversion Hnf; subst.
    exists (subst J (s_sub q e_hole)). split.
    + admit.
    + econstructor 3.
      * apply jred_jmp_cong. apply HM.
      * constructor. constructor.
Admitted.


(* ========================================================================== *)
(* Biorthogonal closure *)

Definition SemType : Type := ∀ S : VSig, value S → Prop.

Class SemTypeClass (R : SemType) := {
  SemType_map {S T : VSig} (φ : prod_arr S T) (V : value S) :
    R S V →
    R T (fmap φ V)
}.

Definition KClo {S : VSig} (R : SemType) (E : ectx S) : Prop :=
  ∀ T (φ : prod_arr S T) (V : value T), R T V → twn (eplug (fmap φ E) V).

Definition EClo {S : VSig} (R : SemType) (M : term S) : Prop :=
  ∀ T (φ : prod_arr S T) (E : ectx T), KClo R E → twn (eplug E (fmap φ M)).

Lemma EClo_value {S : VSig} (R : SemType) {STC : SemTypeClass R} (V : value S) :
  R S V →
  EClo R V.
Proof.
  intro HR.
  intros T φ E HE.
  unfold KClo in HE.
  rewrite <- map_id with (f := ı).
  rewrite eplug_fmap.
  apply HE.
  - term_simpl. rewrite map_id.
    + apply SemType_map. apply HR.
    + reflexivity.
  - reflexivity.
Qed.

Lemma KClo_map {S T : VSig} (R : SemType) (φ : prod_arr S T) (E : ectx S) :
  KClo R E →
  KClo R (fmap φ E).
Proof.
  intros HE U ψ V HV.
  rewrite map_map_comp'.
  apply HE.
  apply HV.
Qed.

(* ========================================================================== *)
(* Denotation of types *)

Reserved Notation "'⟦' A '⟧'".

Definition RelAtom : SemType :=
  λ S V, twn V.

Program Instance SemTypeClass_Atom : SemTypeClass RelAtom.
Next Obligation.
  unfold RelAtom.
Admitted.

Definition RelBot : SemType :=
  λ S V, False.

Program Instance SemTypeClass_Bot : SemTypeClass RelBot.

Definition RelArrow (R₁ R₂ : SemType) : SemType :=
  λ S V, (∀ V', R₁ S V' → EClo R₂ (t_app V V')).

Program Instance SemTypeClass_Arrow : ∀ R₁ R₂, SemTypeClass (RelArrow R₁ R₂).
Next Obligation.
Admitted.

Fixpoint relT (A : ttype) : SemType :=
  λ S, match A with
  | tp_atom _ => RelAtom S
  | tp_bottom => RelBot S
  | tp_arrow A B => RelArrow ⟦ A ⟧ ⟦ B ⟧ S
  end
where "⟦ A ⟧" := (relT A).

Definition RelCont {S : VSig} (R : SemType) :=
  @KClo S R.

Definition relK {S : VSig} (A : ktype) :=
  match A with
  | tp_cont A => @RelCont S ⟦ A ⟧
  end.

Notation "'⟦¬' A '⟧'" := (relK A).

Definition envlog {S T : VSig} (Γ : env S) (φ : S {→} T) :=
  (∀ x, ⟦ env_v Γ x ⟧ T (sub_v φ x))
  ∧ (∀ k, let (_, E) := sub_k φ k in ⟦¬ (env_k Γ k) ⟧ E).

Notation "'G⟦' Γ '⟧'" := (envlog Γ).

Definition tlog {S : VSig} (Γ : env S) (M : term S) (A : ttype) : Prop :=
  ∀ T (φ : S {→} T), G⟦ Γ ⟧ φ → EClo ⟦ A ⟧ (bind φ M).

Notation "'T⟦' Γ '⊨' M '∷' A '⟧'" := (@tlog _ Γ M A).

Definition jlog {S : VSig} (Γ : env S) (J : jump S) : Prop :=
  let (q, M) := J in
  ∀ A T (φ : S {→} T), G⟦ Γ ⟧ φ → EClo ⟦ A ⟧ (bind φ M).

Notation "'J⟦' Γ '⊨' J '∷' ⊥⊥ '⟧'" := (@jlog _ Γ J).

(* Definition klog {S : VSig} (Γ : env S) (q : katom S) (A : ttype) : Prop :=
  ∀ T (φ : S {→} T), envlog Γ φ → RelCont ⟦ A ⟧ q. *)

(* Notation "'K⟦' Γ '⊨' q '∷' A '→⊥⊥' '⟧'" := (@klog _ Γ q A). *)

Lemma compat_var {S : VSig} (Γ : env S) x :
  T⟦ Γ ⊨ v_var x ∷ env_v Γ x ⟧.
Proof.
  intros T φ HΓ.
  apply EClo_value.
  - destruct (env_v Γ x); term_simpl.
    + apply SemTypeClass_Atom.
    + apply SemTypeClass_Bot.
    + apply SemTypeClass_Arrow.
  - apply HΓ.
Qed.

Lemma compat_app_cl {S : VSig} (M₁ M₂ : term S) (R₁ R₂ : SemType) :
  EClo (RelArrow R₂ R₁) M₁ →
  EClo R₂ M₂ →
  EClo R₁ (t_app M₁ M₂).
Proof.
  intros HM₁ HM₂.
  unfold EClo. intros T φ E HE.
  replace (t_app M₁ M₂) with (eplug (e_appl e_hole M₂) M₁) by reflexivity.
  rewrite eplug_fmap.
  rewrite eplug_plug_comp.
  apply HM₁. intros U ψ V HV.
  rewrite <- ecomp_fmap.
  rewrite <- eplug_plug_comp. term_simpl.
  replace (t_app V (fmap ψ (fmap φ M₂))) with (eplug (e_appr V e_hole) (fmap ψ (fmap φ M₂))) by reflexivity.
  rewrite eplug_plug_comp.
  rewrite map_map_comp'.
  unfold EClo in HM₂.
  apply HM₂. intros U' ψ' V' HV'.
  rewrite <- ecomp_fmap.
  rewrite <- eplug_plug_comp. term_simpl.
  rewrite <- map_id with (f := ı); [| reflexivity ].
  rewrite eplug_fmap.
  apply SemType_map with (φ := ψ') in HV.
  unfold RelArrow, EClo in HV.
  refine (HV V' _ U' _ _ _).
  - apply HV'.
  - rewrite map_id; [| reflexivity ].
    rewrite map_map_comp'.
    apply KClo_map.
    apply HE.
Qed.

Lemma compat_app {S : VSig} (Γ : env S) M₁ M₂ τ₁ τ₂ :
  T⟦ Γ ⊨ M₁ ∷ tp_arrow τ₂ τ₁ ⟧ →
  T⟦ Γ ⊨ M₂ ∷ τ₂ ⟧ →
  T⟦ Γ ⊨ t_app M₁ M₂ ∷ τ₁ ⟧.
Proof.
  intros HM₁ HM₂ T φ HΓ.
  eapply compat_app_cl.
  - apply HM₁. apply HΓ.
  - apply HM₂. apply HΓ.
Qed.

Lemma compat_lam {S : VSig} (Γ : env S) M τ₁ τ₂ :
  T⟦ Γ ↦ᵥ τ₂ ⊨ M ∷ τ₁ ⟧ →
  T⟦ Γ ⊨ v_lam M ∷ tp_arrow τ₂ τ₁ ⟧.
Proof.
  intro HM.
  intros T φ HΓ. term_simpl.
  apply EClo_value; [ apply SemTypeClass_Arrow |].
  unfold RelArrow.
  intros V' HV'.
  intros U ψ E HE.
  eapply twn_red.
  - apply tred_plug. constructor.
  - term_simpl.
    remember (mk_subst V') as sb. remember (@lift VSig _ _ _ _ _ φ) as φ'.
    rewrite <- fmap_subst.
    unfold subst.
    rewrite bind_bind_comp'.
    apply HM; [| assumption ].
    destruct HΓ as [HΓᵥ HΓₖ].
    split.
    + intro x. destruct x.
      * subst sb φ'. term_simpl. apply HV'.
      * subst sb φ'. term_simpl. apply HΓᵥ.
    + intro k. specialize HΓₖ with k.
      subst sb φ'. simpl.
      destruct (sub_k φ k) as [q F]. term_simpl.
      destruct q; term_simpl; apply HΓₖ.
Qed.

Definition eshift {S : VSig} (E : ectx S) : ectx (incK S) := shift E.

Lemma compat_ctrl {S : VSig} (Γ : env S) J A :
  J⟦ Γ ↦ₖ tp_cont A ⊨ J ∷ ⊥⊥ ⟧ →
  T⟦ Γ ⊨ t_ctrl J ∷ A ⟧.
Proof.
  intro HJ.
  intros T φ HΓ. term_simpl.
  unfold jlog in HJ.
  intros U ψ E HE.
  term_simpl.

  apply twn_plug_ctrl.

  destruct J.
  destruct q.
  - destruct k.
    + term_simpl. unfold struct_subst. term_simpl.
      apply twn_jwn.
      
      rewrite bind_bind_comp'.
      unfold EClo in HJ. apply HJ with (A := A).
      * constructor.
        -- intro x. term_simpl. unfold envlog in HΓ. admit.
        -- intro k. destruct k.
          ++ term_simpl. rewrite ecomp_pure.
            unfold RelCont. admit.
          ++ term_simpl. destruct (sub_k φ π). term_simpl.
            destruct q; term_simpl.
            ** admit.
            ** admit.
      * 
Qed.

Lemma compat_tp {S : VSig} (Γ : env S) M :
  T⟦ Γ ⊨ M ∷ tp_bottom ⟧ →
  J⟦ Γ ⊨ j_jmp k_tp M ∷ ⊥⊥ ⟧.
Proof.
  intro HM.
  intros T φ A. term_simpl.
  intros E HE.
  unfold tlog in HM.
  specialize HM with (incK T) φ. term_simpl in HM.
  unfold EClo in HM.
  eapply twn_red.
  - apply tred_plug. 



Theorem tfundamental_property {S : VSig} (Γ : env S) M A :
  T[ Γ ⊢ M ∷ A ] →
  T⟦ Γ ⊨ M ∷ A ⟧
 with jfundamental_property {S : VSig} (Γ : env S) J :
  J[ Γ ⊢ J ∷ ⊥⊥ ] →
  J⟦ Γ ⊨ J ∷ ⊥⊥ ⟧.
Proof.
(* t *)
{
  intro Htyp.
  induction Htyp.
  - subst. apply compat_var.
  - eapply compat_app; eassumption.
  - apply compat_lam. assumption.
  - apply jfundamental_property in H as IHJ.
    apply compat_ctrl.
    apply IHJ.
}
(* j *)
{
  intro Htyp.
  induction Htyp.
  - apply tfundamental_property in H as
}
Qed.
  

Lemma tlog_norm {S : VSig} (Γ : env S) (A : ttype) (M : term S) :
  T⟦ Γ ⊨ M ∷ A ⟧ →
  twn M
 with jlog_norm {S : VSig} (Γ : env S) (J : jump S) :
  J⟦ Γ ⊨ J ∷ ⊥⊥ ⟧ →
  jwn J.
Proof.
(* tlog_norm *)
{
  intro Hlog.
  unfold tlog in Hlog.
  specialize Hlog with S (arrow_id (ArrowCore := ArrowCore_VSub) S).
  unfold EClo in Hlog.
  specialize Hlog with S (arrow_id (ArrowCore := ArrowCore_vsig_arr (AC₁ := ArrowCore_Set) (AC₂ := ArrowCore_Set)) S) e_hole.
  rewrite map_id in Hlog; [| reflexivity ].
  rewrite bind_pure in Hlog; [| reflexivity ].
  simpl eplug in Hlog.
  apply Hlog.
  admit.
}
(* jlog_norm *)
{
  intro Hlog.
  destruct J.
  apply twn_jwn.
  unfold jlog in Hlog.
  
}
