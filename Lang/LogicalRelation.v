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

Fixpoint twn_reds {S : VSig} (M₁ M₂ : term S)
  (Hreds: M₁ →*ₜ M₂) { struct Hreds } :
  twn M₂ →
  twn M₁.
Proof.
  intros Hwn.
  inversion Hreds; subst.
  - eapply twn_red.
    + apply H.
    + apply Hwn.
  - apply Hwn.
  - apply twn_reds in H0; [| apply Hwn ].
    apply twn_reds in H; [| apply H0 ].
    apply H.
Qed.

Lemma twn_plug {S : VSig} E (M₁ M₂ : term S) :
  M₁ →*ₜ M₂ →
  twn (eplug E M₂) →
  twn (eplug E M₁).
Proof.
  intros Hreds Hwn.
  eapply twn_reds.
  - apply tred_plug_cong. apply Hreds.
  - apply Hwn.
Qed.

Lemma twn_lam {S : VSig} (M : term (incV S)) :
  twn M →
  twn (v_lam M).
Proof.
  intro HM.
  destruct HM as [V [Hnf Hred]].
  exists (v_lam V). split.
  - constructor. constructor. apply Hnf.
  - apply tred_value_cong. apply vred_lam_cong. apply Hred.
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

(* Lemma twn_jwn {S : VSig} q (M : term S) :
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
Admitted. *)


(* ========================================================================== *)
(* Biorthogonal closure *)

Definition SemType {S : VSig} : Type := value S → Prop.

Definition KClo {S : VSig} (R : SemType) (E : ectx S) : Prop :=
  ∀ V, R V → twn (eplug E V).

Definition EClo {S : VSig} (R : SemType) (M : term S) : Prop :=
  ((∃ V : value S, M →*ₜ V ∧ R V)
   ∨ (∃ J, M →*ₜ t_ctrl J ∧ (∀ E, KClo R E → jwn (struct_subst J (shift E))))).

Definition JClo {S : VSig} (R : @SemType S) (J : jump S) : Prop :=
  True.

Lemma EClo_value {S : VSig} (R : SemType) (V : value S) :
  R V →
  EClo R V.
Proof.
  intro HR.
  unfold EClo.
  left. exists V.
  split.
  - constructor 2.
  - apply HR.
Qed.

(* Lemma KClo_map {S T : VSig} (R : SemType) (φ : prod_arr S T) (E : ectx S) :
  KClo R E →
  KClo R (fmap φ E).
Proof.
  intros HE U ψ V HV.
  rewrite map_map_comp'.
  apply HE.
  apply HV.
Qed. *)

(* ========================================================================== *)
(* Denotation of types *)

Reserved Notation "'⟦' A '⟧'".

Definition RelAtom {S : VSig} : SemType :=
  λ V : value S, twn V.

Definition RelBot {S : VSig} : SemType :=
  λ V : value S, False.

Definition RelArrow {S : VSig} (R₁ R₂ : SemType) : SemType :=
  λ V : value S, twn V ∧ (∀ V', R₁ V' → EClo R₂ (t_app V V')).

Fixpoint relT {S : VSig} (A : ttype) : SemType :=
  match A with
  | tp_atom _ => @RelAtom S
  | tp_bottom => RelBot
  | tp_arrow A B => RelArrow ⟦ A ⟧ ⟦ B ⟧
  end
where "⟦ A ⟧" := (@relT _ A).

(* Lemma EClo_value {S : VSig} (A : ttype) (V : value S) :
  ⟦ A ⟧ V →
  EClo ⟦ A ⟧ V.
Proof.
  intro HV.
  destruct A.
  - term_simpl in *. unfold EClo, RelAtom in *.
    repeat split.
    + apply HV.
    + left. destruct HV as [V' [HnfV Hred]].
      apply treds_value_inv in Hred as HV'.
      destruct HV' as [U]; subst; rename U into V'.
      exists V'. split.
      * apply Hred.
      * exists V'. split; [ assumption | constructor 2].
  - destruct HV.
  - term_simpl in *. unfold EClo, RelArrow in *.
    destruct HV as [Hwn HV].
    repeat split.
    + apply Hwn.
    + left. destruct Hwn as [V' [HnfV' Hred]].
      apply treds_value_inv in Hred as HV'ᵥ.
      destruct HV'ᵥ as [U]; subst; rename U into V'.
      exists V'. split; [| split ].
      * apply Hred.
      * exists V'. split; [ assumption | constructor 2 ].
      * intros U HU. specialize HV with U.
        apply HV in HU.
        unfold EClo in *.
        destruct HU as [HnfU HU].
        unfold twn in HnfU.
        split.
        -- 

 *)

Definition RelCont {S : VSig} (R : SemType) :=
  @KClo S R.

Definition relK {S : VSig} (A : ktype) :=
  match A with
  | tp_cont A => @RelCont S ⟦ A ⟧
  end.

Notation "'⟦' A '→⊥⊥' '⟧'" := (relK A).

Definition relG {S T : VSig} (Γ : env S) (φ : S {→} T) :=
  (∀ x, ⟦ env_v Γ x ⟧ (sub_v φ x))
  ∧ (∀ k, let (_, E) := sub_k φ k in ⟦ (env_k Γ k) →⊥⊥ ⟧ E).

Notation "'G⟦' Γ '⟧'" := (@relG _ _ Γ).

Definition tlog {S : VSig} (Γ : env S) (M : term S) (A : ttype) : Prop :=
  ∀ T (φ : S {→} T), G⟦ Γ ⟧ φ → EClo ⟦ A ⟧ (bind φ M).

Notation "'T⟦' Γ '⊨' M '∷' A '⟧'" := (@tlog _ Γ M A).

Definition jlog {S : VSig} (Γ : env S) (J : jump S) : Prop :=
  let (q, M) := J in
  ∀ T (φ : S {→} T) A, G⟦ Γ ⟧ φ → K[ Γ ⊢ q ∷ A →⊥⊥ ] → JClo ⟦ A ⟧ (bind φ J).

Notation "'J⟦' Γ '⊨' J '∷' ⊥⊥ '⟧'" := (@jlog _ Γ J).

Lemma compat_var {S : VSig} (Γ : env S) x :
  T⟦ Γ ⊨ v_var x ∷ env_v Γ x ⟧.
Proof.
  intros T φ HΓ.
  term_simpl.
  apply EClo_value.
  apply HΓ.
Qed.

Lemma twn_EK {S : VSig} (M : term S) E R :
  EClo R M →
  KClo R E →
  twn (eplug E M).
Proof.
  intros HE HK.
  unfold EClo in HE. destruct HE as [[V [Hred HV]] | [J [Hred HJ]]].
  - eapply twn_plug.
    + apply Hred.
    + apply HK. apply HV.
  - eapply twn_plug.
    + apply Hred.
    + apply twn_plug_ctrl. apply HJ. apply HK.
Qed.

Lemma compat_app_cl {S : VSig} (M₁ M₂ : term S) (R₁ R₂ : SemType) :
  EClo (RelArrow R₂ R₁) M₁ →
  EClo R₂ M₂ →
  EClo R₁ (t_app M₁ M₂).
Proof.
  intros HM₁ HM₂.
  unfold EClo in *.
  destruct HM₁ as [HM₁ | HM₁], HM₂ as [HM₂ | HM₂].
  - destruct HM₁ as [V₁ [Hred₁ HV₁]].
    destruct HM₂ as [V₂ [Hred₂ HV₂]].
    unfold RelArrow in HV₁.
    destruct HV₁ as [Hwn₁ HV₁].
    specialize HV₁ with V₂. apply HV₁ in HV₂.
    unfold EClo in HV₂.
    destruct HV₂ as [HV₂ | HV₂].
    + destruct HV₂ as [V [Hred HV]].
      left. exists V. split.
      * econstructor 3.
        { apply tred_app_cong; [ apply Hred₁ | apply Hred₂ ]. }
        apply Hred.
      * apply HV.
    + destruct HV₂ as [J [Hred HJ]].
      right. exists J. split.
      * econstructor 3.
        { apply tred_app_cong; [ apply Hred₁ | apply Hred₂ ]. }
        apply Hred.
      * apply HJ.
  - destruct HM₁ as [V₁ [Hred₁ HV₁]].
    destruct HM₂ as [J₂ [Hred₂ HJ₂]].
    right. exists (struct_subst J₂ (e_appr (shift V₁) e_hole)). split.
    + econstructor 3.
      { apply tred_app_cong; [ apply Hred₁ | apply Hred₂ ]. }
      constructor. constructor.
    + intros E HE.
      rewrite struct_subst_comp with (E₁ := e_appr V₁ e_hole).
      remember (ecomp E (e_appr V₁ e_hole)) as E'.
      specialize HJ₂ with E'.
      apply HJ₂.
      unfold KClo. intros V₂ HV₂. subst E'.
      rewrite <- eplug_plug_comp; simpl.
      unfold RelArrow in HV₁. destruct HV₁ as [Hwn₁ HV₁].
      specialize HV₁ with V₂. apply HV₁ in HV₂.
      eapply twn_EK.
      * apply HV₂.
      * apply HE.
  - destruct HM₁ as [J₁ [Hred₁ HJ₁]].
    destruct HM₂ as [V₂ [Hred₂ HV₂]].
    right. exists (struct_subst J₁ (shift (e_appl e_hole V₂))). split.
    + econstructor 3.
      { apply tred_app_cong; [ apply Hred₁ | apply Hred₂ ]. }
      constructor. constructor.
    + intros E HE.
      rewrite struct_subst_comp. apply HJ₁. unfold KClo.
      intros V HV.
      rewrite <- eplug_plug_comp; simpl.
      unfold RelArrow in HV. destruct HV as [Hwn HV].
      specialize HV with V₂. apply HV in HV₂.
      eapply twn_EK.
      * apply HV₂.
      * apply HE.
  - destruct HM₁ as [J₁ [Hred₁ HJ₁]].
    destruct HM₂ as [J₂ [Hred₂ HJ₂]].
    right. exists (struct_subst J₁ (shift (e_appl e_hole (t_ctrl J₂)))). split.
    + econstructor 3.
      { apply tred_app_cong; [ apply Hred₁ | apply Hred₂ ]. }
      constructor. constructor.
    + intros E HE.
      rewrite struct_subst_comp. apply HJ₁.
      unfold KClo. intros V HV.
      rewrite <- eplug_plug_comp; simpl.
      eapply twn_plug.
      { constructor. constructor. }
      apply twn_plug_ctrl.
      rewrite struct_subst_comp with (E₁ := e_appr V e_hole).
      apply HJ₂. intros V' HV'.
      rewrite <- eplug_plug_comp; simpl.
      unfold RelArrow in HV. destruct HV as [Hwn HV].
      apply HV in HV'.
      eapply twn_EK.
      * apply HV'.
      * apply HE.
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
  apply EClo_value.
  unfold tlog in HM.
  (* specialize HM with (incV T) (@lift _ _ _ LiftableCore_sub_incV _ _ φ). *)
  (* assert (Hlift: G⟦ Γ ↦ᵥ τ₂ ⟧ (φ ↑ᵥ)).
  { unfold relG. split.
    - intro x. destruct x as [| x ].
      + simpl. 
      + simpl. unfold relG in HΓ. apply HΓ.
    - intro k. simpl. apply HΓ. } *)
  unfold RelArrow. split.
  - apply twn_lam. admit.
  - intros V' HV'. left.
    unfold EClo in HM.
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
  intros U ψ E HE.
  term_simpl.

  apply twn_plug_ctrl.

  destruct J.

  inversion HJ; subst.

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
