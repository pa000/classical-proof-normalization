Require Import Utf8.
Require Import Binding.Lib Binding.Product Binding.Set.
Require Import Syntax Semantics.
Require Import Relation_Operators.

(* Formalization based on:
    [1] Baba Kensuke, Sachio Hirokawa, Ken-Etsu Fujita:
        Parallel Reduction in Type Free λμ-Calculus. Electronic Notes in Theoretical Computer Science. 2001;42:52–66.
    [2] Herman Geuvers, Robbert Krebbers, James McKinna:
        The λμᵀ-calculus. Annals of Pure and Applied Logic. 2012;164(6):676-701.
    [3] Programming Language Foundations in Agda - Confluence:
        https://plfa.inf.ed.ac.uk/Confluence/
*)

Reserved Notation "M '⇉ₜ' M'" (at level 67).
Reserved Notation "V '⇉ᵥ' V'" (at level 67).
Reserved Notation "J '⇉ⱼ' J'" (at level 67).
Reserved Notation "E '⇉ₑ' E'" (at level 67).

(* We prove confluence in the typical way by defining a parallel reduction relation ⇉.
  It corresponds to reducing many redexes in a term simultaneously. We then show that:
    - ⇉ is confluent (by defining a complete development),
    - ⇉ ⊆ →* ⊆ ⇉*,
  which implies that the original reduction is confluent.

  It's worth to note that the naive definition of ⇉ doesn't work [1].
  To fix this, a slight change is needed for the rule jpar_C_idem. *)
Inductive tpar {S : VSig} : term S → term S → Prop :=
  | tpar_beta : ∀ M M' (V V' : value S),
    M ⇉ₜ M' →
    V ⇉ᵥ V' →
    t_app (v_lam M) V ⇉ₜ subst M' V'
  | tpar_C_L : ∀ J J' N N',
    J ⇉ⱼ J' →
    N ⇉ₜ N' →
    t_app (t_ctrl J) N ⇉ₜ t_ctrl (struct_subst J' (e_appl e_hole (shift N')))
  | tpar_C_R : ∀ J J' (V V' : value S),
    J ⇉ⱼ J' →
    V ⇉ᵥ V' →
    t_app V (t_ctrl J) ⇉ₜ t_ctrl (struct_subst J' (e_appr (shift V') e_hole))

  | tpar_value : ∀ V V',
    V ⇉ᵥ V' →
    V ⇉ₜ V'
  | tpar_app : ∀ M M' N N',
    M ⇉ₜ M' →
    N ⇉ₜ N' →
    t_app M N ⇉ₜ t_app M' N'
  | tpar_ctrl : ∀ J J',
    J ⇉ⱼ J' →
    t_ctrl J ⇉ₜ t_ctrl J'
with vpar {S : VSig} : value S → value S → Prop :=
  | vpar_var : ∀ x,
    v_var x ⇉ᵥ v_var x
  | vpar_lam : ∀ M M',
    M ⇉ₜ M' →
    v_lam M ⇉ᵥ v_lam M'
with jpar {S : VSig} : jump S → jump S → Prop :=
  (* The naive definition would be:
        j_jmp q (t_ctrl J) ⇉ⱼ subst J' (s_sub q e_hole).
     However, this doesn't work. We need to generalize it for any evaluation context. *)
  | jpar_C_idem : ∀ (q : katom S) E E' J J',
    J ⇉ⱼ J' →
    E ⇉ₑ E' →
    j_jmp q (eplug E (t_ctrl J)) ⇉ⱼ subst J' (s_sub q E')

  | jpar_jmp : ∀ q M M',
    M ⇉ₜ M' →
    j_jmp q M ⇉ⱼ j_jmp q M'
with epar {S : VSig} : ectx S → ectx S → Prop :=
  | epar_hole :
    e_hole ⇉ₑ e_hole
  | epar_appl : ∀ E E' M M',
    E ⇉ₑ E' →
    M ⇉ₜ M' →
    e_appl E M ⇉ₑ e_appl E' M'
  | epar_appr : ∀ V V' E E',
    V ⇉ᵥ V' →
    E ⇉ₑ E' →
    e_appr V E ⇉ₑ e_appr V' E'

where "M ⇉ₜ M'" := (tpar M M')
  and "V ⇉ᵥ V'" := (vpar V V')
  and "J ⇉ⱼ J'" := (jpar J J')
  and "E ⇉ₑ E'" := (epar E E').

Notation tpar_rtc M₁ M₂ := (clos_refl_trans _ tpar M₁ M₂).
Notation vpar_rtc V₁ V₂ := (clos_refl_trans _ vpar V₁ V₂).
Notation jpar_rtc J₁ J₂ := (clos_refl_trans _ jpar J₁ J₂).

Notation "M '⇉*ₜ' M'" := (tpar_rtc M M') (at level 50).
Notation "J '⇉*ⱼ' J'" := (jpar_rtc J J') (at level 50).
Notation "V '⇉*ᵥ' V'" := (vpar_rtc V V') (at level 50).

Lemma tpar_eplug {S : VSig} (E E' : ectx S) (M M' : term S) :
  E ⇉ₑ E' →
  M ⇉ₜ M' →
  eplug E M ⇉ₜ eplug E' M'.
Proof.
  intros HparE HparM.
  induction HparE;
    repeat (term_simpl; constructor || auto).
Qed.

Lemma tpar_lam_invert {S : VSig} (M M' : term (incV S)) :
  v_lam M ⇉ₜ v_lam M' →
  M ⇉ₜ M'.
Proof.
  intro Hpar.
  inversion Hpar; subst.
  inversion H1; subst.
  apply H2.
Qed.

Lemma tpar_value_invert {S : VSig} (V V' : value S) :
  V ⇉ₜ V' →
  V ⇉ᵥ V'.
Proof.
  intro Hpar. inversion Hpar; assumption.
Qed.

Lemma tpar_ctrl_invert {S : VSig} (J J' : jump (incK S)) :
  t_ctrl J ⇉ₜ t_ctrl J' →
  J ⇉ⱼ J'.
Proof.
  intro Hpar. inversion Hpar; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* ⇉ is reflexive. *)

Lemma tpar_refl {S : VSig} : ∀ (M : term S),
  M ⇉ₜ M
with vpar_refl {S : VSig} : ∀ (V : value S),
  V ⇉ᵥ V
with jpar_refl {S : VSig} : ∀ (J : jump S),
  J ⇉ⱼ J.
Proof.
(* tpar_refl *)
{
  induction M.
  + constructor. apply vpar_refl.
  + constructor.
    - apply IHM1.
    - apply IHM2.
  + constructor. apply jpar_refl.
}
(* vpar_refl *)
{
  induction V.
  + constructor.
  + constructor. apply tpar_refl.
}
(* jpar_refl *)
{
  induction J.
  constructor. apply tpar_refl.
}
Qed.

Lemma epar_refl {S : VSig} : ∀ (E : ectx S),
  E ⇉ₑ E.
Proof.
  intro E.
  induction E; constructor; assumption || apply tpar_refl || apply vpar_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* → ⊆ ⇉ and →* ⊆ ⇉*. *)

Lemma tred_par {S : VSig} : ∀ (M N : term S),
  M →ₜ N →
  M ⇉ₜ N
with vred_par {S : VSig} : ∀ (V V' : value S),
  V →ᵥ V' →
  V ⇉ᵥ V'
with jred_par {S : VSig} : ∀ (J J' : jump S),
  J →ⱼ J' →
  J ⇉ⱼ J'.
Proof.
(* tred_par *)
{
  intros M N Hred.
  induction Hred.
  + constructor 1 with (V' := V).
    - apply tpar_refl.
    - apply vpar_refl.
  + constructor.
    - apply jpar_refl.
    - apply tpar_refl.
  + econstructor.
    - apply jpar_refl.
    - apply vpar_refl.
  + constructor.
    apply vred_par. apply H.
  + constructor.
    - apply IHHred.
    - apply tpar_refl.
  + constructor.
    - apply tpar_refl.
    - apply IHHred.
  + constructor.
    apply jred_par. apply H.
}
(* vred_par *)
{
  intros V V' Hred.
  induction Hred.
  constructor.
  apply tred_par. apply H.
}
(* jred_par *)
{
  intros J J' Hred.
  induction Hred.
  + econstructor 1 with (E := e_hole).
    - apply jpar_refl.
    - apply epar_refl.
  + constructor.
    apply tred_par. apply H.
}
Qed.

Lemma treds_pars {S : VSig} : ∀ (M N : term S),
  M →*ₜ N →
  M ⇉*ₜ N
with vreds_pars {S : VSig} : ∀ (V V' : value S),
  V →*ᵥ V' →
  V ⇉*ᵥ V'
with jreds_pars {S : VSig} : ∀ (J J' : jump S),
  J →*ⱼ J' →
  J ⇉*ⱼ J'.
Proof.
(* treds_pars *)
{
  intros M N Hreds.
  induction Hreds.
  + constructor. apply tred_par. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
(* vreds_pars *)
{
  intros V V' Hreds.
  induction Hreds.
  + constructor. apply vred_par. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
(* jreds_pars *)
{
  intros J J' Hreds.
  induction Hreds.
  + constructor. apply jred_par. apply H.
  + constructor 2.
  + econstructor 3.
    - apply IHHreds1.
    - apply IHHreds2.
}
Qed.

(* -------------------------------------------------------------------------- *)
(* ⇉ ⊆ →* and ⇉* ⊆ →*. *)

Lemma tpar_reds {S : VSig} (M N : term S) :
  M ⇉ₜ N →
  M →*ₜ N
with vpar_reds {S : VSig} (V V' : value S) :
  V ⇉ᵥ V' →
  V →*ᵥ V'
with jpar_reds {S : VSig} (J J' : jump S) :
  J ⇉ⱼ J' →
  J →*ⱼ J'
with epar_reds {S : VSig} (E E' : ectx S) M :
  E ⇉ₑ E' →
  eplug E M →*ₜ eplug E' M.
Proof.
(* tpar_reds *)
{
  intro Hpar.
  induction Hpar.
  + constructor 3 with (y := t_app (v_lam M') V).
    { apply tred_appl_cong.
      apply tred_value_cong.
      apply vred_lam_cong.
      apply IHHpar. }
    constructor 3 with (y := t_app (v_lam M') V').
    { apply tred_appr_cong.
      apply tred_value_cong.
      apply vpar_reds.
      apply H. }
    constructor. constructor.
  + constructor 3 with (y := t_app (t_ctrl J') N).
    { apply tred_appl_cong.
      apply tred_ctrl_cong.
      apply jpar_reds.
      apply H. }
    constructor 3 with (y := t_app (t_ctrl J') N').
    { apply tred_appr_cong.
      apply IHHpar. }
    constructor. constructor.
  + constructor 3 with (y := t_app V' (t_ctrl J)).
    { apply tred_appl_cong.
      apply tred_value_cong.
      apply vpar_reds.
      apply H0. }
    constructor 3 with (y := t_app V' (t_ctrl J')).
    { apply tred_appr_cong.
      apply tred_ctrl_cong.
      apply jpar_reds.
      apply H. }
    constructor. constructor.
  + apply tred_value_cong.
    apply vpar_reds.
    apply H.
  + constructor 3 with (y := t_app M' N).
    - apply tred_appl_cong.
      apply IHHpar1.
    - apply tred_appr_cong.
      apply IHHpar2.
  + apply tred_ctrl_cong.
    apply jpar_reds.
    apply H.
}
(* vpar_reds *)
{
  intro Hpar.
  induction Hpar.
  + constructor 2.
  + apply vred_lam_cong.
    apply tpar_reds.
    apply H.
}
(* jpar_reds *)
{
  intro Hpar.
  induction Hpar.
  + constructor 3 with (y := j_jmp q (eplug E (t_ctrl J'))).
    { apply jred_jmp_cong.
      apply tred_plug_cong.
      apply tred_ctrl_cong.
      apply IHHpar. }
    econstructor 3.
    { apply jred_jmp_cong.
      apply epar_reds.
      apply H. }
    econstructor 3.
    { apply jred_jmp_cong.
      apply treds_ctrl_plug. }
    econstructor 3.
    { constructor. constructor. }
    rewrite subst_struct_subst.
    term_simpl. constructor 2.
  + apply jred_jmp_cong.
    apply tpar_reds.
    apply H.
}
(* epar_reds *)
{
  intro Hpar.
  induction Hpar.
  + term_simpl. constructor 2.
  + term_simpl.
    econstructor 3.
    { apply tred_appl_cong.
      apply IHHpar. }
    econstructor 3.
    { apply tred_appr_cong.
      apply tpar_reds.
      apply H. }
    constructor 2.
  + term_simpl.
    econstructor 3.
    { apply tred_appr_cong.
      apply IHHpar. }
    econstructor 3.
    { apply tred_appl_cong.
      apply tred_value_cong.
      apply vpar_reds.
      apply H. }
    econstructor 2.
}
Qed.

Lemma tpars_reds {S : VSig} (M N : term S) :
  M ⇉*ₜ N →
  M →*ₜ N
with vpars_reds {S : VSig} (V V' : value S) :
  V ⇉*ᵥ V' →
  V →*ᵥ V'
with jpars_reds {S : VSig} (J J' : jump S) :
  J ⇉*ⱼ J' →
  J →*ⱼ J'.
Proof.
all: (
  intros Hpar;
  induction Hpar; [
    apply tpar_reds || apply vpar_reds || apply jpar_reds; apply H
  | constructor 2
  | econstructor 3; [
      apply IHHpar1
    | apply IHHpar2 ]]).
Qed.

(* -------------------------------------------------------------------------- *)
(* complete development *)

(* The complete development is obtained by contracting all redexes of a term. *)
Fixpoint tcd {S : VSig} (M : term S) { struct M } : term S :=
  match M with
  | t_value V => t_value (vcd V)
  | t_app (v_lam M₁) (t_value V₂) => subst (tcd M₁) (vcd V₂)
  | t_app (t_ctrl J) M₂ => t_ctrl (struct_subst (jcd J) (e_appl e_hole (shift (tcd M₂))))
  | t_app (t_value V₁) (t_ctrl J) => t_ctrl (struct_subst (jcd J) (e_appr (shift (vcd V₁)) e_hole))
  | t_app M₁ M₂ => t_app (tcd M₁) (tcd M₂)
  | t_ctrl J => t_ctrl (jcd J)
  end
with vcd {S : VSig} (V : value S) { struct V } : value S :=
  match V with
  | v_var x => v_var x
  | v_lam M => v_lam (tcd M)
  end
with jcd {S : VSig} (J : jump S) { struct J } : jump S :=
  match J with
  | j_jmp q M =>
    match unplug_ctrl M with
    | Some (E, J) => subst J (s_sub q E)
    | None => j_jmp q (tcd M)
    end
  end
(* return Some (ecd E, jcd J) iff M = eplug E (t_ctrl J) *)
with unplug_ctrl {S : VSig} (M : term S) : option (ectx S * jump (incK S)) :=
  match M with
  | t_value V => None
  | t_app (t_value V₁) M₂ =>
    match unplug_ctrl M₂ with
    | Some (E, J) => Some (e_appr (vcd V₁) E, J)
    | None => None
    end
  | t_app M₁ M₂ =>
    match unplug_ctrl M₁ with
    | Some (E, J) => Some (e_appl E (tcd M₂), J)
    | None => None
    end
  | t_ctrl J => Some (e_hole, jcd J)
  end.

Fixpoint ecd {S : VSig} (E : ectx S) : ectx S :=
  match E with
  | e_hole => e_hole
  | e_appl E M => e_appl (ecd E) (tcd M)
  | e_appr V E => e_appr (vcd V) (ecd E)
  end.

Lemma unplug_ctrl_correct1 {S : VSig} (M : term S) :
  ∀ E J, unplug_ctrl M = Some (E, J)
  → (∀ E' J', M = eplug E' (t_ctrl J') → ecd E' = E ∧ jcd J' = J).
Proof.
  intros E J Hunplug F K HM.
  induction M as [ S V | S M₁ IHM₁ M₂ | S J' ].
  + discriminate Hunplug.
  + destruct M₁ as [ V₁ | N₁ N₂ | J₂ ].
    - term_simpl in Hunplug.
      destruct (unplug_ctrl M₂) as [[E' J'] |]; [| discriminate ].
      inversion Hunplug as [[HE' HJ']]; clear HE'.
      rewrite HJ' in *; clear HJ'.
      destruct F; try discriminate.
      * destruct F; try discriminate.
      * term_simpl in HM.
        specialize IHM₂ with E' J F K.
        inversion HM as [[HV₁ HM₂]].
        destruct (IHM₂ (eq_refl (Some (E', J))) HM₂) as [HF HK].
        split; [| apply HK ].
        term_simpl. f_equal. apply HF.
    - term_simpl in Hunplug.
      destruct N₁ as [ V₁ | U₁ U₂ | J₁ ].
      * destruct (unplug_ctrl N₂) as [[E' J'] |] eqn:HunN₂; [| discriminate ].
        inversion Hunplug as [[HE' HJ']]; clear HE'.
        rewrite HJ' in *; clear HJ'.
        destruct F; try discriminate.
        term_simpl in HM.
        inversion HM as [[HV₁ HM₂]].
        specialize IHM₁ with (e_appr (vcd V₁) E') J F K.
        apply IHM₁ in HV₁ as [HF HK].
        { split; [| apply HK ]. term_simpl.
          f_equal. apply HF. }
        { term_simpl. rewrite HunN₂. reflexivity. }
      * destruct (unplug_ctrl (t_app U₁ U₂)) as [[E' J'] |] eqn:Hunapp; [| discriminate ].
        inversion Hunplug as [[HE' HJ']]; clear HE'.
        rewrite HJ' in *; clear HJ'.
        destruct F; try discriminate.
        term_simpl in HM.
        inversion HM as [[Happ HM₂]].
        specialize IHM₁ with (e_appl E' (tcd N₂)) J F K.
        apply IHM₁ in Happ as [HF HK].
        { split; [| apply HK ]. term_simpl.
          f_equal. apply HF. }

        remember (t_app U₁ U₂) as N₁.
        term_simpl. destruct N₁; try discriminate; rewrite HeqN₁ in *.
        rewrite Hunapp. reflexivity.
      * term_simpl in Hunplug.
        inversion Hunplug as [[HE HJ]]; clear HE.
        rewrite HJ in *.
        destruct F; try discriminate.
        inversion HM as [[Happ HM₂]].
        specialize IHM₁ with (e_appl e_hole (tcd N₂)) J F K.
        apply IHM₁ in Happ as [HF HK].
        { split; [| apply HK ]. term_simpl.
          f_equal. apply HF. }

        term_simpl. rewrite HJ. reflexivity.
    - term_simpl in Hunplug.
      inversion Hunplug as [[HE HJ]]; clear HE.
      destruct F; try discriminate.
      inversion HM as [[Hctrl HM₂]].
      specialize IHM₁ with e_hole (jcd J₂) F K.
      apply IHM₁ in Hctrl as [HF HK].
      { split; [| apply HK ]. term_simpl.
        f_equal. apply HF. }

      term_simpl. reflexivity.
  + term_simpl in Hunplug.
    inversion Hunplug as [[HE HJ]].
    destruct F; try discriminate.
    inversion HM.
    auto.
Qed.

Lemma unplug_ctrl_correct2 {S : VSig} (M : term S) E' J' E J :
  M = eplug E' (t_ctrl J') →
  ecd E' = E →
  jcd J' = J →
  unplug_ctrl M = Some (E, J).
Proof.
  intros HM HE HJ.
  induction M as [ S V | S M₁ IHM₁ M₂ | S K ].
  + destruct E'; discriminate.
  + destruct M₁ as [ V₁ | N₁ N₂ | J₂ ].
    - destruct E'; try discriminate.
      { term_simpl in HM. destruct E'; try discriminate. }
      term_simpl in HE.
      destruct E as [| | v' E ]; try discriminate.
      inversion HE as [[Hvcd Hecd]].
      inversion HM as [[HV₁ HM₂]]. rewrite <- HM₂.
      specialize IHM₂ with E' J' (ecd E') J.
      apply IHM₂ in HM₂; [| reflexivity | apply HJ ]. term_simpl.
      destruct (unplug_ctrl M₂) as [[F K] |]; [| discriminate ].
      inversion HM₂ as [[HF HK]].
      reflexivity.
    - destruct E'; try discriminate.
      term_simpl in HE.
      destruct E as [| F t' |]; try discriminate.
      inversion HE as [[Hecd Htcd]].
      inversion HM as [[Happ HM₂]].
      specialize IHM₁ with E' J' (ecd E') J.
      apply IHM₁ in Happ; [| reflexivity | apply HJ ].

      remember (t_app N₁ N₂) as M₁.
      term_simpl. destruct M₁; try discriminate; rewrite HeqM₁ in *.

      rewrite Happ. reflexivity.
    - destruct E'; try discriminate.
      term_simpl in HE.
      destruct E as [| F t' |]; try discriminate.
      inversion HE as [[Hecd Htcd]].
      inversion HM as [[Hctrl HM₂]].
      specialize IHM₁ with E' J' (ecd E') J.
      apply IHM₁ in Hctrl; [| reflexivity | apply HJ ].
      term_simpl. term_simpl in Hctrl.
      inversion Hctrl.
      reflexivity.
  + term_simpl.
    destruct E'; try discriminate; subst.
    term_simpl in HM.
    inversion HM; subst.
    reflexivity.
Qed.

Lemma unplug_ctrl_plug {S : VSig} (E : ectx S) J :
  unplug_ctrl (eplug E (t_ctrl J)) = Some (ecd E, jcd J).
Proof.
  destruct (unplug_ctrl (eplug E (t_ctrl J))) as [[E' J'] |] eqn:Hunplug.
  + apply unplug_ctrl_correct1 with (E' := E) (J' := J) in Hunplug as [HE HJ].
    - rewrite HE, HJ.
      reflexivity.
    - reflexivity.
  + pose proof (@unplug_ctrl_correct2 S) as Hcorrect.
    specialize Hcorrect with (eplug E (t_ctrl J)) E J (ecd E) (jcd J).
    destruct (Hcorrect (eq_refl (eplug E (t_ctrl J)))).
    - reflexivity.
    - reflexivity.
    - symmetry. apply Hunplug.
Qed.

Lemma unplug_ctrl_some {S : VSig} (M : term S) E J :
  unplug_ctrl M = Some (E, J) →
  ∃ E' J', M = eplug E' (t_ctrl J') ∧ ecd E' = E ∧ jcd J' = J.
Proof.
  intro Hsome.
  induction M as [ S V | S M₁ IHM₁ M₂ | S J' ].
  + term_simpl in Hsome. discriminate.
  + term_simpl in Hsome.
    destruct M₁ as [ V₁ | N₁ N₂ | J₂ ].
    - destruct (unplug_ctrl M₂) as [[F K] |]; [| discriminate ].
      inversion Hsome as [[HF HK]].
      specialize IHM₂ with F K.
      destruct (IHM₂ (eq_refl (Some (F, K)))) as [F' [K' [HM₂ [Hecd Hjcd]]]].
      exists (e_appr V₁ F'), K'.
      repeat split.
      * term_simpl. f_equal. apply HM₂.
      * term_simpl. f_equal. apply Hecd.
      * rewrite <- HK. apply Hjcd.
    - destruct (unplug_ctrl (t_app N₁ N₂)) as [[F K] |]; [| discriminate ].
      inversion Hsome as [[HF HK]].
      specialize IHM₁ with F K.
      destruct (IHM₁ (eq_refl (Some (F, K)))) as [F' [K' [Happ [Hecd Hjcd]]]].
      exists (e_appl F' M₂), K'.
      repeat split.
      * term_simpl. f_equal. apply Happ.
      * term_simpl. f_equal. apply Hecd.
      * rewrite <- HK. apply Hjcd.
    - term_simpl in Hsome.
      inversion Hsome as [[HE HJ]].
      exists (e_appl e_hole M₂), J₂.
      repeat split.
  + term_simpl in Hsome.
    inversion Hsome as [[HE HJ]].
    exists e_hole, J'.
    repeat split.
Qed.

(* -------------------------------------------------------------------------- *)
(* every term parallel-reduces to its complete development. *)

(* In the proof of jpar_cd (below) we have a term that we know is of the form
    M = eplug E (t_ctrl J). We then need to prove that E ⇉ₑ ecd E and J ⇉ⱼ jcd J.
    When proving this on paper, we could just use the induction hypothesis.
    However, Coq's termination checker won't allow that. Instead, we prove
    that it holds for every subterm of M (subterms_cd M) and then use standalone
    lemmas to get the desired properties. *)
Fixpoint subterms_cd {S : VSig} (M : term S) : Prop :=
  match M with
  | t_app M₁ M₂ =>
    M₁ ⇉ₜ tcd M₁
    ∧ M₂ ⇉ₜ tcd M₂
    ∧ subterms_cd M₁
    ∧ subterms_cd M₂
  | _ => True
  end.

Lemma epar_cd_plug_ind {S : VSig} (M : term S) E :
  subterms_cd (eplug E M) →
  E ⇉ₑ ecd E.
Proof.
  intros Hsubterms.
  induction E as [| E IHE N | V E IHE ].
  + apply epar_refl.
  + term_simpl. term_simpl in Hsubterms.
    destruct Hsubterms as [Hplug_cd [HN_cd [Hplug_subterms _]]].
    constructor.
    - apply IHE. apply Hplug_subterms.
    - apply HN_cd.
  + term_simpl. term_simpl in Hsubterms.
    destruct Hsubterms as [HV_cd [Hplug_cd [_ Hplug_subterms]]].
    constructor.
    - apply tpar_value_invert.
      apply HV_cd.
    - apply IHE. apply Hplug_subterms.
Qed.

Lemma tpar_cd_plug_ind {S : VSig} (M : term S) E :
  eplug E M ⇉ₜ tcd (eplug E M) →
  subterms_cd (eplug E M) →
  M ⇉ₜ tcd M.
Proof.
  intros HMcd Hsubterms.
  induction E as [| E IHE N | V E IHE ].
  + apply HMcd.
  + term_simpl. term_simpl in Hsubterms.
    destruct Hsubterms as [Hplug_cd [HN_cd [Hplug_subterms _]]].
    apply IHE.
    - apply Hplug_cd.
    - apply Hplug_subterms.
  + term_simpl. term_simpl in Hsubterms.
    destruct Hsubterms as [HV_cd [Hplug_cd [_ Hplug_subterms]]].
    apply IHE.
    - apply Hplug_cd.
    - apply Hplug_subterms.
Qed.

Lemma tpar_cd {S : VSig} (M : term S) :
  M ⇉ₜ tcd M
with vpar_cd {S : VSig} (V : value S) :
  V ⇉ᵥ vcd V
with jpar_cd {S : VSig} (J : jump S) :
  J ⇉ⱼ jcd J.
Proof.
(* treds_cd *)
{
  induction M as [ ? V | A M₁ IHM₁ M₂ |].
  + term_simpl. constructor. apply vpar_cd.
  + term_simpl. destruct M₁ as [V | N₁ N₂ |].
    - term_simpl. destruct V as [ x | M ].
      * term_simpl. destruct M₂ as [ V | N₁ N₂ | J ].
        ++ term_simpl. constructor.
          -- apply tpar_refl.
          -- constructor.
            inversion IHM₂ as [| | | ? ? IHV | |]; subst.
            apply IHV.
        ++ constructor.
          -- apply tpar_refl.
          -- apply IHM₂.
        ++ apply tpar_C_R with (V' := v_var x).
          -- inversion IHM₂ as [| | | | | ? ? IHj ]; subst.
            apply IHj.
          -- apply vpar_refl.
      * destruct M₂ as [V | N₁ N₂ | J ].
        ++ term_simpl. constructor.
          -- simpl in IHM₁.
            inversion IHM₁ as [| | | ? ? IHM₁ᵥ | |]; subst.
            inversion IHM₁ᵥ as [| ? ? IHt ]; subst.
            apply IHt.
          -- inversion IHM₂ as [| | | ? ? IHM₂ᵥ | |]; subst.
            apply IHM₂ᵥ.
        ++ constructor.
          -- apply IHM₁.
          -- apply IHM₂.
        ++ constructor.
          -- simpl in IHM₂.
            inversion IHM₂ as [| | |  | | ? ? IHJ ]; subst.
            apply IHJ.
          -- inversion IHM₁; subst.
            apply H1.
    - constructor.
      * apply IHM₁.
      * apply IHM₂.
    - constructor.
      * inversion IHM₁ as [| | | | | ? ? IHj ]; subst.
        apply IHj.
      * apply IHM₂.
  + term_simpl. constructor.
    apply jpar_cd.
}
(* vpar_cd *)
{
  induction V as [x | M].
  + term_simpl. apply vpar_refl.
  + term_simpl. constructor.
    apply tpar_cd.
}
(* jpar_cd *)
{
  induction J as [q M].
  + term_simpl. destruct (unplug_ctrl M) as [[E J] |] eqn:Hunplug.
    - term_simpl. apply unplug_ctrl_some in Hunplug.
      destruct Hunplug as [E' [J' [HM [HE HJ]]]].

      assert (Hsubterms: subterms_cd (eplug E' (t_ctrl J'))).
      { rewrite <- HM.
        clear HM HE HJ J E' J' E q.
        induction M.
        + term_simpl. apply I.
        + term_simpl. repeat split.
          - apply tpar_cd.
          - apply tpar_cd.
          - apply IHM1.
          - apply IHM2.
        + term_simpl. apply I. }

      rewrite HM. constructor.
      * rewrite <- HJ.

        apply tpar_ctrl_invert.
        apply tpar_cd_plug_ind with (M := t_ctrl J') (E := E').
        ++ rewrite <- HM. apply tpar_cd.
        ++ apply Hsubterms.
      * rewrite <- HE.
        apply epar_cd_plug_ind with (M := t_ctrl J') (E := E').
        apply Hsubterms.
    - constructor. apply tpar_cd.
}
Qed.

Lemma epar_cd {S : VSig} (E : ectx S) :
  E ⇉ₑ ecd E.
Proof.
  induction E; term_simpl; constructor; auto using tpar_cd, vpar_cd.
Qed.

(* -------------------------------------------------------------------------- *)
(* ⇉ is preserved under fmap. *)

Lemma tpar_map {S T : VSig} (φ : prod_arr S T) (M M' : term S) :
  M ⇉ₜ M' →
  fmap φ M ⇉ₜ fmap φ M'
 with vpar_map {S T : VSig} (φ : prod_arr S T) (V V' : value S) :
  V ⇉ᵥ V' →
  fmap φ V ⇉ᵥ fmap φ V'
 with jpar_map {S T : VSig} (φ : prod_arr S T) (J J' : jump S) :
  J ⇉ⱼ J' →
  fmap φ J ⇉ⱼ fmap φ J'
 with epar_map {S T : VSig} (φ : prod_arr S T) (E E' : ectx S) :
  E ⇉ₑ E' →
  fmap φ E ⇉ₑ fmap φ E'.
Proof.
(* tpar_map *)
{
  intros Hpar.
  generalize dependent T.
  induction Hpar; intros T φ;
    try (term_simpl; constructor; auto).
  + term_simpl. rewrite fmap_struct_subst with (E := e_appl e_hole N').
    term_simpl. constructor.
    - apply jpar_map. apply H.
    - apply IHHpar.
  + term_simpl. rewrite fmap_struct_subst with (E := e_appr V' e_hole).
    term_simpl. constructor.
    - apply jpar_map. apply H.
    - apply vpar_map. apply H0.
}
(* vpar_map *)
{
  intros Hpar.
  induction Hpar;
    try (term_simpl; constructor; auto).
}
(* jpar_map *)
{
  intros Hpar.
  induction Hpar;
    try (term_simpl; constructor; auto).
  + term_simpl. rewrite eplug_fmap.
    constructor. term_simpl.
    - apply jpar_map. apply Hpar.
    - apply epar_map. apply H.
}
(* epar_map *)
{
  intros Hpar.
  induction Hpar;
    (term_simpl; constructor; auto).
}
Qed.

(* -------------------------------------------------------------------------- *)
(* ⇉ is preserved under bind (substitution).
   We use an auxiliary definition of parallel reduction for substitutions. *)

Definition sspar {S : VSig} (s s' : ssub S) :=
  let (q₁, E₁) := s  in
  let (q₂, E₂) := s' in
  q₁ = q₂ ∧ E₁ ⇉ₑ E₂.

Notation "s ⇉ₛₛ s'" := (sspar s s') (at level 67).

Lemma sspar_map {S T : VSig} (s s' : ssub S) (φ : prod_arr S T) :
  s ⇉ₛₛ s' →
  fmap φ s ⇉ₛₛ fmap φ s'.
Proof.
  intro Hpar.
  destruct s as [q E].
  destruct s' as [q' E'].
  constructor.
  + f_equal. apply Hpar.
  + apply epar_map. apply Hpar.
Qed.

Lemma sspar_vshift {S : VSig} (s s' : ssub S) :
  s ⇉ₛₛ s' →
  shift (Inc := incV) s ⇉ₛₛ shift s'.
Proof.
  intro Hpar.
  apply sspar_map. apply Hpar.
Qed.

Lemma sspar_kshift {S : VSig} (s s' : ssub S) :
  s ⇉ₛₛ s' →
  shift s ⇉ₛₛ shift s'.
Proof.
  intro Hpar.
  apply sspar_map. apply Hpar.
Qed.

Lemma sspar_refl {S : VSig} (s : ssub S) :
  s ⇉ₛₛ s.
Proof.
  unfold sspar.
  destruct s; split; auto using epar_refl.
Qed.

Definition spar {S T : VSig} (φ φ' : S {→} T) :=
  (∀ x, sub_v φ x ⇉ᵥ sub_v φ' x)
  ∧ (∀ k, sub_k φ k ⇉ₛₛ sub_k φ' k).
Notation "φ ⇉ₛ φ'" := (spar φ φ') (at level 67).

Notation "t ↑ᵥ" := (lift (G := incV) t) (at level 15).

Lemma spar_vlift {S T : VSig} (φ φ' : S {→} T) :
  φ ⇉ₛ φ' →
  φ ↑ᵥ ⇉ₛ φ' ↑ᵥ.
Proof.
  intros Hpar.
  destruct Hpar as [Hx Hk].
  constructor.
  + intro x. destruct x as [| x].
    - term_simpl. apply vpar_refl.
    - term_simpl. apply vpar_map. apply Hx.
  + intro k. term_simpl. apply sspar_vshift. apply Hk.
Qed.

Lemma spar_refl {S T : VSig} (φ : S {→} T) :
  φ ⇉ₛ φ.
Proof.
  constructor; intro; auto using vpar_refl, sspar_refl.
Qed.

Lemma spar_klift {S T : VSig} (φ φ' : S {→} T) :
  φ ⇉ₛ φ' →
  φ ↑ ⇉ₛ φ' ↑.
Proof.
  intros Hpar.
  destruct Hpar as [Hx Hk].
  constructor.
  + intro x. term_simpl. apply vpar_map. apply Hx.
  + intro k. destruct k as [| k].
    - term_simpl. split; [ reflexivity | apply epar_refl ].
    - term_simpl. apply sspar_kshift. apply Hk.
Qed.

Lemma epar_comp {S : VSig} (E₂ E₂' E₁ E₁' : ectx S) :
  E₂ ⇉ₑ E₂' →
  E₁ ⇉ₑ E₁' →
  ecomp E₂ E₁ ⇉ₑ ecomp E₂' E₁'.
Proof.
  intros Hpar₂ Hpar₁.
  induction Hpar₂.
  + term_simpl. apply Hpar₁.
  + term_simpl. constructor.
    - apply IHHpar₂. apply Hpar₁.
    - apply H.
  + term_simpl. constructor.
    - apply H.
    - apply IHHpar₂. apply Hpar₁.
Qed.

Lemma tpar_bind {S T : VSig} (M M' : term S) (φ φ' : S {→} T) :
  φ ⇉ₛ φ' →
  M ⇉ₜ M' →
  bind φ M ⇉ₜ bind φ' M'
 with vpar_bind {S T : VSig} (V V' : value S) (φ φ' : S {→} T) :
  φ ⇉ₛ φ' →
  V ⇉ᵥ V' →
  bind φ V ⇉ᵥ bind φ' V'
 with jpar_bind {S T : VSig} (J J' : jump S) (φ φ' : S {→} T) :
  φ ⇉ₛ φ' →
  J ⇉ⱼ J' →
  bind φ J ⇉ⱼ bind φ' J'
 with epar_bind {S T : VSig} (E E' : ectx S) (φ φ' : S {→} T) :
  φ ⇉ₛ φ' →
  E ⇉ₑ E' →
  bind φ E ⇉ₑ bind φ' E'.
Proof.
(* tpar_bind *)
{
  intros Hφ Hpar.
  generalize dependent T.
  induction Hpar; intros T φ φ' Hφ.
  + term_simpl. constructor.
    - apply IHHpar. apply spar_vlift. apply Hφ.
    - apply vpar_bind.
      * apply Hφ.
      * apply H.
  + term_simpl.
    rewrite bind_struct_subst with (E := e_appl e_hole N').
    rewrite bind_liftS_shift_comm. term_simpl.
    constructor.
    - apply jpar_bind.
      * apply spar_klift. apply Hφ.
      * apply H.
    - apply IHHpar. apply Hφ.
  + term_simpl.
    rewrite bind_struct_subst with (E := e_appr V' e_hole).
    replace (e_appr (shift V) e_hole) with (shift (e_appr V e_hole)) by reflexivity.
    term_simpl.
    constructor.
    - apply jpar_bind.
      * apply spar_klift. apply Hφ.
      * apply H.
    - apply vpar_bind.
      * apply Hφ.
      * apply H0.
  + term_simpl. constructor.
    apply vpar_bind.
    - apply Hφ.
    - apply H.
  + term_simpl. constructor.
    - apply IHHpar1. apply Hφ.
    - apply IHHpar2. apply Hφ.
  + term_simpl. constructor.
    apply jpar_bind.
    - apply spar_klift. apply Hφ.
    - apply H.
}
(* vpar_bind *)
{
  intros Hφ Hpar.
  induction Hpar.
  + term_simpl. apply Hφ.
  + term_simpl. constructor.
    apply tpar_bind.
    - apply spar_vlift. apply Hφ.
    - apply H.
}
(* jpar_bind *)
{
  intros Hφ Hpar.
  generalize dependent T.
  induction Hpar; intros T φ φ' Hφ.
  + term_simpl. destruct q as [k |].
    - pose proof Hφ as [_ Hk].
      specialize Hk with k.

      destruct (sub_k φ k) as [q F].
      destruct (sub_k φ' k) as [q' F'].

      rewrite <- eplug_bind.
      rewrite eplug_plug_comp.

      destruct Hk as [Hq HF].
      rewrite Hq.

      constructor; term_simpl.
      * apply IHHpar. apply spar_klift. apply Hφ.
      * apply epar_comp; [ apply HF |].
        apply epar_bind; [ apply Hφ | apply H ].
    - rewrite <- eplug_bind.
      constructor; term_simpl.
      * term_simpl. apply IHHpar. apply spar_klift. apply Hφ.
      * apply epar_bind; [ apply Hφ | apply H ].
  + term_simpl. destruct q as [k |].
    - pose proof Hφ as [_ Hk].
      specialize Hk with k.

      destruct (sub_k φ k) as [q E].
      destruct (sub_k φ' k) as [q' E'].

      destruct Hk as [Hq HE].
      rewrite Hq.
      constructor. apply tpar_eplug; [ apply HE |].
      apply tpar_bind; [ apply Hφ | apply H ].
    - constructor. apply tpar_bind; [ apply Hφ | apply H ].
}
(* epar_bind *)
{
  intros Hφ Hpar.
  induction Hpar.
  + apply epar_refl.
  + term_simpl. constructor.
    - apply IHHpar. apply Hφ.
    - apply tpar_bind; [ apply Hφ | apply H ].
  + term_simpl. constructor.
    - apply vpar_bind; [ apply Hφ | apply H ].
    - apply IHHpar. apply Hφ.
}
Qed.

Lemma spar_mk_subst_value {S : VSig} (V V' : value S) :
  V ⇉ᵥ V' →
  mk_subst V ⇉ₛ mk_subst V'.
Proof.
  intros Hpar.
  constructor.
  + intro x. destruct x as [| x].
    - term_simpl. apply Hpar.
    - term_simpl. apply vpar_refl.
  + intro k. term_simpl. split; [ reflexivity | apply epar_refl ].
Qed.

Lemma spar_mk_subst_ectx {S : VSig} q (E E' : ectx S) :
  E ⇉ₑ E' →
  mk_subst (s_sub q E) ⇉ₛ mk_subst (s_sub q E').
Proof.
  intro Hpar.
  constructor.
  + intro x. term_simpl. apply vpar_refl.
  + intro k. destruct k as [| k].
    - term_simpl. auto.
    - term_simpl. split.
      * reflexivity.
      * apply epar_refl.
Qed.

Lemma tpar_subst {S : VSig} (M M' : term (incV S)) V V' :
  M ⇉ₜ M' →
  V ⇉ᵥ V' →
  subst M V ⇉ₜ subst M' V'.
Proof.
  intros HparM HparV.
  apply tpar_bind.
  + apply spar_mk_subst_value. apply HparV.
  + apply HparM.
Qed.

Lemma spar_struct_sub {S : VSig} (E E' : ectx (incK S)) :
  E ⇉ₑ E' →
  struct_sub E ⇉ₛ struct_sub E'.
Proof.
  intro Hpar.
  constructor.
  + intro x. term_simpl. apply vpar_refl.
  + intro k. destruct k as [| k].
    - term_simpl. split; [ reflexivity | apply Hpar ].
    - term_simpl. split; [ reflexivity | apply epar_refl ].
Qed.

Lemma jpar_struct_subst {S : VSig} (J J' : jump (incK S)) E E' :
  J ⇉ⱼ J' →
  E ⇉ₑ E' →
  struct_subst J E ⇉ⱼ struct_subst J' E'.
Proof.
  intros HparJ HparE.
  apply jpar_bind.
  + apply spar_struct_sub. apply HparE.
  + apply HparJ.
Qed.

Lemma jpar_subst {S : VSig} q (J J' : jump (incK S)) E E' :
  J ⇉ⱼ J' →
  E ⇉ₑ E' →
  subst J (s_sub q E) ⇉ⱼ subst J' (s_sub q E').
Proof.
  intros HparJ HparE.
  apply jpar_bind.
  + apply spar_mk_subst_ectx. apply HparE.
  + apply HparJ.
Qed.

(* -------------------------------------------------------------------------- *)
(* triangle lemma:
   if M ⇉ M', then M' ⇉ tcd M.
      M
     /|
    / |
   M' |
    \ |
     \|
    tcd M
*)

Lemma tpar_eplug_invert {S : VSig} (E : ectx S) J M :
  eplug E (t_ctrl J) ⇉ₜ M →
  (∃ E' M', M = eplug E' M' ∧ t_ctrl J ⇉ₜ M' ∧ E ⇉ₑ E')
  ∨ (∃ E' E'' J', M = eplug E'' (t_ctrl (struct_subst J' (shift E'))) ∧ J ⇉ⱼ J' ∧ E ⇉ₑ ecomp E'' E').
Proof.
  intro Hpar.
  generalize dependent M.
  induction E; intros M Hpar.
  + term_simpl in Hpar.
    inversion Hpar; subst.
    left.
    exists e_hole, (t_ctrl J').
    repeat split.
    - constructor. apply H0.
    - apply epar_refl.
  + term_simpl in Hpar.
    inversion Hpar; subst.
    - destruct E; discriminate.
    - destruct E; try discriminate.
      term_simpl in Hpar.
      inversion H; subst; clear H.
      right.
      exists (e_appl e_hole N'), e_hole, J'.
      repeat split.
      * apply H1.
      * constructor; [ apply epar_refl | apply H3 ].
    - destruct E; discriminate.
    - apply IHE in H1. destruct H1.
      * destruct H as [E' [U [HM' [HJ HE]]]].
        inversion HJ; subst.
        left.
        exists (e_appl E' N'), (t_ctrl J').
        repeat split.
        ++ constructor. apply H0.
        ++ constructor; [ apply HE | apply H3 ].
      * destruct H as [E' [E'' [J' [HM' [HJ HE]]]]]; subst.
        right.
        exists E', (e_appl E'' N'), J'.
        repeat split.
        ++ apply HJ.
        ++ term_simpl. constructor; [ apply HE | apply H3 ].
  + term_simpl in Hpar.
    inversion Hpar; subst.
    - destruct E; discriminate.
    - destruct E; try discriminate.
      inversion H0; subst; clear H0.
      right.
      exists (e_appr V' e_hole), e_hole, J'.
      repeat split.
      * apply H1.
      * term_simpl. constructor; [ apply H3 | apply epar_refl ].
    - apply IHE in H3. destruct H3.
      * destruct H as [E' [U [HN' [HJ HE]]]]; subst.
        inversion HJ; subst.
        inversion H1; subst.
        left.
        exists (e_appr V' E'), (t_ctrl J').
        repeat split.
        ++ constructor. apply H0.
        ++ constructor; [ apply H2 | apply HE ].
      * destruct H as [E' [E'' [J' [HN' [HJ HE]]]]]; subst.
        inversion H1; subst.
        right.
        exists E', (e_appr V' E''), J'.
        repeat split.
        ++ apply HJ.
        ++ term_simpl. constructor; [ apply H0 | apply HE ].
Qed.

Lemma epar_comp_invert {S : VSig} (E E₁ E₂ : ectx S) :
  E ⇉ₑ ecomp E₂ E₁ →
  ∃ F₂ F₁, E = ecomp F₂ F₁ ∧ F₂ ⇉ₑ E₂ ∧ F₁ ⇉ₑ E₁.
Proof.
  intro Hpar.
  generalize dependent E₁.
  generalize dependent E₂.
  induction E as [| E IHE M | V E IHE ]; intros E₂ E₁ Hpar.
  + inversion Hpar.
    destruct E₂; try discriminate.
    destruct E₁; try discriminate.
    exists e_hole, e_hole.
    repeat split; apply epar_refl.
  + inversion Hpar; subst.
    destruct E₂; try discriminate.
    - apply IHE with (E₂ := e_hole) in H2.
      destruct H2 as [F₂ [F₁ [HE [HF₂ HF₁]]]].
      inversion HF₂; subst.
      term_simpl in H1; term_simpl; term_simpl in Hpar.
      exists e_hole, (e_appl F₁ M).
      repeat split.
      * apply epar_refl.
      * apply Hpar.
    - term_simpl in H1.
      inversion H1; subst.
      apply IHE in H2.
      destruct H2 as [F₂ [F₁ [HE [HF₂ HF₁]]]]; subst.
      exists (e_appl F₂ M), F₁.
      repeat split.
      * constructor; [ apply HF₂ | apply H3 ].
      * apply HF₁.
  + inversion Hpar; subst.
    destruct E₂; try discriminate.
    - apply IHE with (E₂ := e_hole) in H3.
      destruct H3 as [F₂ [F₁ [HE [HF₂ HF₁]]]]; subst.
      inversion HF₂; subst.
      term_simpl; term_simpl in H1; term_simpl in Hpar.
      exists e_hole, (e_appr V F₁).
      repeat split.
      * apply epar_refl.
      * apply Hpar.
    - term_simpl in H1.
      inversion H1; subst.
      apply IHE in H3.
      destruct H3 as [F₂ [F₁ [HE [HF₂ HF₁]]]]; subst.
      exists (e_appr V F₂), F₁.
      repeat split.
      * constructor; [ apply H2 | apply HF₂ ].
      * apply HF₁.
Qed.

Lemma ecd_ecomp {S : VSig} (E₂ E₁ : ectx S) :
  ecd (ecomp E₂ E₁) = ecomp (ecd E₂) (ecd E₁).
Proof.
  induction E₂; term_simpl; f_equal; assumption.
Qed.

(* We satisfy the termination checker in a similar way as with subterms_cd. *)
Fixpoint subterms_tcd {S : VSig} (M : term S) : Prop :=
  match M with
  | t_app M₁ M₂ =>
    (∀ N₁, M₁ ⇉ₜ N₁ → N₁ ⇉ₜ tcd M₁)
    ∧ (∀ N₂, M₂ ⇉ₜ N₂ → N₂ ⇉ₜ tcd M₂)
    ∧ subterms_tcd M₁
    ∧ subterms_tcd M₂
  | _ => True
  end.

Lemma ecd_complete_plug_ind {S : VSig} (M : term S) E :
  subterms_tcd (eplug E M) →
  (∀ E', E ⇉ₑ E' → E' ⇉ₑ ecd E).
Proof.
  intro Htcd.
  generalize dependent M.
  induction E as [| E IHE N | V E IHE ]; intros M Htcd E' Hpar.
  + inversion Hpar. apply epar_refl.
  + term_simpl in Htcd.
    destruct Htcd as [Hplug_tcd [HN_tcd [Hplug_subterms HN_subterms]]].
    inversion Hpar as [| ? F ? N' HE HN |]; subst.
    simpl ecd. constructor.
    - apply IHE with M.
      * apply Hplug_subterms.
      * apply HE.
    - apply HN_tcd. apply HN.
  + term_simpl in Htcd.
    destruct Htcd as [HV_tcd [Hplug_tcd [HV_subterms Hplug_subterms]]].
    inversion Hpar as [| | ? V' ? F HV HE ]; subst.
    simpl ecd. constructor.
    - specialize HV_tcd with (t_value V').
      apply tpar_value in HV.
      apply HV_tcd in HV.
      Transparent tcd.
      inversion HV; subst.
      apply H1.
    - apply IHE with M.
      * apply Hplug_subterms.
      * apply HE.
Qed.

Lemma ecd_complete_plug_comp_ind {S : VSig} (M : term S) E₂ E₁ :
  subterms_tcd (eplug (ecomp E₂ E₁) M) →
  (∀ F₁, E₁ ⇉ₑ F₁ → F₁ ⇉ₑ ecd E₁)
  ∧ (∀ F₂, E₂ ⇉ₑ F₂ → F₂ ⇉ₑ ecd E₂).
Proof.
  intro Htcd.
  generalize dependent M.
  generalize dependent E₁.
  induction E₂ as [| E IHE N | V E IHE ]; intros E₁ M Htcd.
  + split; intros F Hpar.
    - apply ecd_complete_plug_ind with (E' := F) in Htcd.
      * apply Htcd.
      * apply Hpar.
    - inversion Hpar. apply epar_refl.
  + term_simpl in Htcd.
    destruct Htcd as [Hplug_tcd [HN_tcd [Hplug_subterms HN_subterms]]].
    apply IHE in Hplug_subterms as [HE₁ HE].
    split.
    - apply HE₁.
    - intros F₂ Hpar.
      inversion Hpar; subst.
      term_simpl. constructor.
      * apply HE. apply H1.
      * apply HN_tcd. apply H3.
  + term_simpl in Htcd.
    destruct Htcd as [HV_tcd [Hplug_tcd [_ Hplug_subterms]]].
    apply IHE in Hplug_subterms as [HE₁ HE].
    split.
    - apply HE₁.
    - intros F₂ Hpar.
      inversion Hpar; subst.
      term_simpl. constructor.
      * apply tpar_value_invert.
        apply HV_tcd.
        constructor. apply H1.
      * apply HE. apply H3.
Qed.

Lemma tcd_complete_plug_ind {S : VSig} (M : term S) E :
  (∀ M', eplug E M ⇉ₜ M' → M' ⇉ₜ tcd (eplug E M)) →
  subterms_tcd (eplug E M) →
  (∀ M', M ⇉ₜ M' → M' ⇉ₜ tcd M).
Proof.
  intros Htcd Hstcd.
  generalize dependent M.
  induction E as [| E IHE N | V E IHE ]; intros M Htcd Hstcd M' Hpar.
  + apply Htcd. apply Hpar.
  + term_simpl in Hstcd.
    destruct Hstcd as [Hplug_tcd [HN_tcd [Hplug_subterms HN_subterms]]].
    apply IHE.
    - apply Hplug_tcd.
    - apply Hplug_subterms.
    - apply Hpar.
  + term_simpl in Hstcd.
    destruct Hstcd as [HV_tcd [Hplug_tcd [HV_subterms Hplug_subterms]]].
    apply IHE.
    - apply Hplug_tcd.
    - apply Hplug_subterms.
    - apply Hpar.
Qed.

Transparent tcd.

Fixpoint tcd_complete {S : VSig} (M M' : term S) { struct M }:
  M ⇉ₜ M' →
  M' ⇉ₜ tcd M
 with vcd_complete {S : VSig} (V V' : value S) { struct V }:
  V ⇉ᵥ V' →
  V' ⇉ᵥ vcd V
 with jcd_complete {S : VSig} (J J' : jump S) { struct J }:
  J ⇉ⱼ J' →
  J' ⇉ⱼ jcd J.
Proof.
(* tcd_complete *)
{
  intro Hpar.
  induction M as [ S V | S M₁ IHM₁ M₂ | S J ].
  (* t_value V *)
  + term_simpl. inversion Hpar as [| | | ? V' Hparᵥ | |]; subst.
    constructor. apply vcd_complete. apply Hparᵥ.
  (* t_app M₁ M₂ *)
  + term_simpl. destruct M₁ as [ V | N₁ N₂ | J ].
    (* t_app V M₂ *)
    - destruct V as [ x | N ].
      (* t_app (v_var x) M₂ *)
      * destruct M₂ as [ V | N₁ N₂ | J ].
        (* t_app (v_var x) V *)
        ++ inversion Hpar as [| | | | ? N₁ ? N₂ HN₁ HN₂ |]; subst.
          constructor.
          -- apply IHM₁. apply HN₁.
          -- apply IHM₂. apply HN₂.
        (* t_app (v_var x) (t_app N₁ N₂) *)
        ++ inversion Hpar as [| | | | ? U₁ ? U₂ HU₁ HU₂ |]; subst.
          constructor.
          -- apply IHM₁. apply HU₁.
          -- apply IHM₂. apply HU₂.
        (* t_app (v_var x) (t_ctrl J) *)
        ++ inversion Hpar as [ | | ? J' ? V HJ HV | | ? M₁ ? M₂ HM₁ HM₂ |]; subst.
          -- constructor; term_simpl.
            apply jpar_bind.
            ** apply spar_struct_sub.
              constructor; [| apply epar_refl ].
              inversion HV; subst.
              term_simpl. apply vpar_refl.
            ** apply jcd_complete. apply HJ.
          -- term_simpl.
            inversion HM₁ as [| | | ? ? HM₁ᵥ | |]; subst.
            inversion HM₁ᵥ; subst.
            inversion HM₂ as [| | | | | ? J' HJ ]; subst.
            constructor 3 with (V' := v_var x).
            ** apply jcd_complete. apply HJ.
            ** apply vpar_refl.
      (* t_app (v_lam N) M₂ *)
      * destruct M₂ as [ V | N₁ N₂ | J ].
        (* t_app (v_lam N) V *)
        ++ term_simpl.
          inversion Hpar as [ ? N' ? V' HN HV | | | | ? N₁ ? N₂ HN₁ HN₂ |]; subst.
          -- apply tpar_subst.
            ** apply tpar_lam_invert.
              apply IHM₁.
              constructor. constructor.
              apply HN.
            ** apply vcd_complete. apply HV.
          -- inversion HN₁ as [| | | ? ? HN₁ᵥ | |]; subst.
            inversion HN₁ᵥ as [| ? N' HN ]; subst.
            inversion HN₂ as [| | | ? ? HN₂ᵥ | |]; subst.
            constructor.
            ** apply tpar_lam_invert.
              apply IHM₁.
              apply HN₁.
            ** apply tpar_value_invert.
              apply IHM₂.
              apply HN₂.
        (* t_app (v_lam N) (t_app N₁ N₂) *)
        ++ inversion Hpar as [| | | | ? U₁ ? U₂ HU₁ HU₂ |]; subst.
          constructor.
          -- apply IHM₁. apply HU₁.
          -- apply IHM₂. apply HU₂.
        (* t_app (v_lam N) (t_ctrl J) *)
        ++ inversion Hpar as [| | ? ? ? V HJ HV | | ? N₁ ? N₂ HN₁ HN₂ |]; subst.
          -- constructor. apply jpar_struct_subst.
            ** apply tpar_ctrl_invert.
              apply IHM₂.
              constructor.
              apply HJ.
            ** constructor; [| apply epar_refl ].
              apply vpar_map.
              apply tpar_value_invert.
              apply IHM₁.
              constructor.
              apply HV.
          -- inversion HN₁ as [| | | ? ? HN₁ᵥ | |]; subst.
            inversion HN₁ᵥ as [| ? N' HN' ]; subst.
            inversion HN₂ as [| | | | | ? J' HJ' ]; subst.
            constructor.
            ** apply tpar_ctrl_invert.
              apply IHM₂.
              apply HN₂.
            ** apply tpar_value_invert.
              apply IHM₁.
              apply HN₁.
    (* t_app (t_app N₁ N₂) M₂ *)
    - inversion Hpar as [| | | | a1 U₁ ? U₂ HU₁ HU₂ |]; subst.
      constructor.
      * apply IHM₁. apply HU₁.
      * apply IHM₂. apply HU₂.
    (* t_app (t_ctrl J) M₂ *)
    - inversion Hpar as [| ? J' ? M HJ HM | | | ? N₁ ? N₂ HN₁ HN₂ |]; subst.
      * constructor.
        apply jpar_struct_subst.
        ++ apply tpar_ctrl_invert.
          apply IHM₁.
          constructor.
          apply HJ.
        ++ constructor; [ apply epar_refl |].
          apply tpar_map.
          apply IHM₂. apply HM.
      * inversion HN₁ as [| | | | | ? J' HJ' ]; subst.
        constructor.
        ++ apply tpar_ctrl_invert.
          apply IHM₁.
          apply HN₁.
        ++ apply IHM₂.
          apply HN₂.
  (* t_ctrl J *)
  + inversion Hpar as [| | | | | ? J' HJ' ]; subst.
    term_simpl. constructor.
    apply jcd_complete. apply HJ'.
}
(* vcd_complete *)
{
  intro Hpar.
  induction V as [ x | M ].
  + inversion Hpar; subst.
    term_simpl. apply Hpar.
  + inversion Hpar as [| ? M' HM' ]; subst.
    term_simpl. constructor.
    apply tcd_complete. apply HM'.
}
(* jcd_complete *)
{
  intro Hpar.
  induction J as [q M].

  assert (Hsubterms: subterms_tcd M).
  { clear Hpar J' q.
    induction M.
    + term_simpl. apply I.
    + term_simpl.
      repeat split.
      - apply tcd_complete.
      - apply tcd_complete.
      - apply IHM1.
      - apply IHM2.
    + term_simpl. apply I. }

  assert (IHtcd_complete: ∀ M', M ⇉ₜ M' → M' ⇉ₜ tcd M) by apply tcd_complete.

  inversion Hpar; subst.
  + term_simpl. rewrite unplug_ctrl_plug; term_simpl.

    pose proof (ecd_complete_plug_ind _ _ Hsubterms) as IHecd.

    apply tcd_complete_plug_ind with (M' := t_ctrl J'0) in Hsubterms as HtcdJ.
    inversion HtcdJ; subst.

    apply jpar_subst.
    - apply H2.
    - apply IHecd. apply H3.
    - apply IHtcd_complete.
    - constructor. apply H1.
  + term_simpl. destruct (unplug_ctrl M) as [[E J] |] eqn:Hunplug.
    - term_simpl. apply unplug_ctrl_some in Hunplug.
      destruct Hunplug as [E' [J' [HM [Hecd Hjcd]]]].

      apply tcd_complete in H2 as Htcd.
      rewrite HM in Htcd, H2, Hsubterms, IHtcd_complete.

      apply tpar_eplug_invert in H2 as Hp.
      destruct Hp as [[F' [N' [HN' [HJ' HF']]]] | [F' [F'' [K' [HM' [HK' HF']]]]]].
      * pose proof (ecd_complete_plug_ind _ _ Hsubterms) as IHecd.
        inversion HJ' as [| | | | | ? K HK ]; subst.

        apply tcd_complete_plug_ind with (M' := t_ctrl K) in Hsubterms as HtcdJ.
        inversion HtcdJ; subst.

        constructor.
        ++ apply H1.
        ++ apply IHecd. apply HF'.
        ++ apply IHtcd_complete.
        ++ constructor. apply HK.
      * apply epar_comp_invert in HF'.
        destruct HF' as [G'' [G' [HE' [HG'' HG']]]]. rewrite <- Hecd, HE'. rewrite HM'.

        rewrite HE' in Hsubterms, IHtcd_complete.
        pose proof (ecd_complete_plug_comp_ind _ _ _ Hsubterms) as [HtcdG' HtcdG''].

        apply tcd_complete_plug_ind with (M' := t_ctrl K') in Hsubterms as HtcdJ.
        inversion HtcdJ; subst.

        rewrite ecd_ecomp.
        rewrite <- subst_struct_subst.
        constructor.
        ++ apply jpar_struct_subst.
          -- apply H1.
          -- apply epar_map. apply HtcdG'. apply HG'.
        ++ apply HtcdG''. apply HG''.
        ++ apply IHtcd_complete.
        ++ constructor. apply HK'.
    - constructor. apply tcd_complete. apply H2.
}
Qed.

(* -------------------------------------------------------------------------- *)
(* Finally: ⇉, ⇉* and →* are confluent. *)

Lemma tpar_confluence {S : VSig} (M M₁ M₂ : term S) :
  M ⇉ₜ M₁ →
  M ⇉ₜ M₂ →
  ∃ M', M₁ ⇉ₜ M' ∧ M₂ ⇉ₜ M'
 with vpar_confluence {S : VSig} (V V₁ V₂ : value S) :
  V ⇉ᵥ V₁ →
  V ⇉ᵥ V₂ →
  ∃ V', V₁ ⇉ᵥ V' ∧ V₂ ⇉ᵥ V'
 with jpar_confluence {S : VSig} (J J₁ J₂ : jump S) :
  J ⇉ⱼ J₁ →
  J ⇉ⱼ J₂ →
  ∃ J', J₁ ⇉ⱼ J' ∧ J₂ ⇉ⱼ J'.
Proof.
(* tpar_confluence *)
{
  intros Hpar₁ Hpar₂.
  exists (tcd M).
  split; apply tcd_complete; assumption.
}
(* vpar_confluence *)
{
  intros Hpar₁ Hpar₂.
  exists (vcd V).
  split; apply vcd_complete; assumption.
}
(* jpar_confluence *)
{
  intros Hpar₁ Hpar₂.
  exists (jcd J).
  split; apply jcd_complete; assumption.
}
Qed.

(* Auxiliary strip lemma:
        M
       / \
      /   *
     /     \
    M₁     M₂
     \    /
      *  /
       \/
       M'
*)

Lemma tpars_strip {S : VSig} (M M₁ M₂ : term S) :
  M ⇉ₜ M₁ →
  M ⇉*ₜ M₂ →
  ∃ M', M₁ ⇉*ₜ M' ∧ M₂ ⇉ₜ M'
 with vpars_strip {S : VSig} (V V₁ V₂ : value S) :
  V ⇉ᵥ V₁ →
  V ⇉*ᵥ V₂ →
  ∃ V', V₁ ⇉*ᵥ V' ∧ V₂ ⇉ᵥ V'
 with jpars_strip {S : VSig} (J J₁ J₂ : jump S) :
  J ⇉ⱼ J₁ →
  J ⇉*ⱼ J₂ →
  ∃ J', J₁ ⇉*ⱼ J' ∧ J₂ ⇉ⱼ J'.
Proof.
(* tpars_strip *)
{
  intros Hpar₁ Hpars₂.
  generalize dependent M₁.
  induction Hpars₂; intros M₁ Hpar₁.
  + exists (tcd x).
    split.
    - constructor. apply tcd_complete. apply Hpar₁.
    - apply tcd_complete. apply H.
  + exists (tcd x).
    split.
    - constructor. apply tcd_complete. apply Hpar₁.
    - apply tpar_cd.
  + apply IHHpars₂1 in Hpar₁.
    destruct Hpar₁ as [tcd₁ [HM₁ Hy]].
    apply IHHpars₂2 in Hy.
    destruct Hy as [tcd₂ [Htcd₁ Hz]].
    exists (tcd₂).
    split.
    - constructor 3 with (y := tcd₁).
      * apply HM₁.
      * apply Htcd₁.
    - apply Hz.
}
(* vpars_strip *)
{
  intros Hpar₁ Hpars₂.
  generalize dependent V₁.
  induction Hpars₂; intros V₁ Hpar₁.
  + exists (vcd x).
    split.
    - constructor. apply vcd_complete. apply Hpar₁.
    - apply vcd_complete. apply H.
  + exists (vcd x).
    split.
    - constructor. apply vcd_complete. apply Hpar₁.
    - apply vpar_cd.
  + apply IHHpars₂1 in Hpar₁.
    destruct Hpar₁ as [vcd₁ [HM₁ Hy]].
    apply IHHpars₂2 in Hy.
    destruct Hy as [vcd₂ [Hvcd₁ Hz]].
    exists (vcd₂).
    split.
    - constructor 3 with (y := vcd₁).
      * apply HM₁.
      * apply Hvcd₁.
    - apply Hz.
}
(* jpars_strip *)
{
  intros Hpar₁ Hpars₂.
  generalize dependent J₁.
  induction Hpars₂; intros J₁ Hpar₁.
  + exists (jcd x).
    split.
    - constructor. apply jcd_complete. apply Hpar₁.
    - apply jcd_complete. apply H.
  + exists (jcd x).
    split.
    - constructor. apply jcd_complete. apply Hpar₁.
    - apply jpar_cd.
  + apply IHHpars₂1 in Hpar₁.
    destruct Hpar₁ as [jcd₁ [HM₁ Hy]].
    apply IHHpars₂2 in Hy.
    destruct Hy as [jcd₂ [Hjcd₁ Hz]].
    exists (jcd₂).
    split.
    - constructor 3 with (y := jcd₁).
      * apply HM₁.
      * apply Hjcd₁.
    - apply Hz.
}
Qed.

Lemma tpars_confluence {S : VSig} (M M₁ M₂ : term S) :
  M ⇉*ₜ M₁ →
  M ⇉*ₜ M₂ →
  ∃ M', M₁ ⇉*ₜ M' ∧ M₂ ⇉*ₜ M'
 with vpars_confluence {S : VSig} (V V₁ V₂ : value S) :
  V ⇉*ᵥ V₁ →
  V ⇉*ᵥ V₂ →
  ∃ V', V₁ ⇉*ᵥ V' ∧ V₂ ⇉*ᵥ V'
 with jpars_confluence {S : VSig} (J J₁ J₂ : jump S) :
  J ⇉*ⱼ J₁ →
  J ⇉*ⱼ J₂ →
  ∃ J', J₁ ⇉*ⱼ J' ∧ J₂ ⇉*ⱼ J'.
Proof.
(* tpars_confluence *)
{
  intros Hpar₁ Hpar₂.
  generalize dependent M₂.
  induction Hpar₁; intros M₂ Hpar₂.
  + pose proof (tpars_strip _ _ _ H Hpar₂) as Hstrip.
    destruct Hstrip as [Mtcd [Hy HM₂]].
    exists Mtcd.
    split.
    - apply Hy.
    - constructor. apply HM₂.
  + assert (Hpar₁: x ⇉ₜ x) by (apply tpar_refl).
    pose proof (tpars_strip _ _ _ Hpar₁ Hpar₂) as Hstrip.
    destruct Hstrip as [Mtcd [Hx HM₂]].
    exists Mtcd.
    split.
    - apply Hx.
    - constructor. apply HM₂.
  + apply IHHpar₁1 in Hpar₂.
    destruct Hpar₂ as [Mtcd₁ [Hy HM₂]].
    apply IHHpar₁2 in Hy.
    destruct Hy as [Mtcd₂ [Hz HMtcd₁]].
    exists Mtcd₂.
    split.
    - apply Hz.
    - constructor 3 with (y := Mtcd₁).
      * apply HM₂.
      * apply HMtcd₁.
}
(* vpars_confluence *)
{
  intros Hpar₁ Hpar₂.
  generalize dependent V₂.
  induction Hpar₁; intros V₂ Hpar₂.
  + pose proof (vpars_strip _ _ _ H Hpar₂) as Hstrip.
    destruct Hstrip as [Vvcd [Hy HV₂]].
    exists Vvcd.
    split.
    - apply Hy.
    - constructor. apply HV₂.
  + assert (Hpar₁: x ⇉ᵥ x) by (apply vpar_refl).
    pose proof (vpars_strip _ _ _ Hpar₁ Hpar₂) as Hstrip.
    destruct Hstrip as [Vvcd [Hx HV₂]].
    exists Vvcd.
    split.
    - apply Hx.
    - constructor. apply HV₂.
  + apply IHHpar₁1 in Hpar₂.
    destruct Hpar₂ as [Vvcd₁ [Hy HV₂]].
    apply IHHpar₁2 in Hy.
    destruct Hy as [Vvcd₂ [Hz HVvcd₁]].
    exists Vvcd₂.
    split.
    - apply Hz.
    - constructor 3 with (y := Vvcd₁).
      * apply HV₂.
      * apply HVvcd₁.
}
(* jpars_confluence *)
{
  intros Hpar₁ Hpar₂.
  generalize dependent J₂.
  induction Hpar₁; intros J₂ Hpar₂.
  + pose proof (jpars_strip _ _ _ H Hpar₂) as Hstrip.
    destruct Hstrip as [Vvcd [Hy HV₂]].
    exists Vvcd.
    split.
    - apply Hy.
    - constructor. apply HV₂.
  + assert (Hpar₁: x ⇉ⱼ x) by (apply jpar_refl).
    pose proof (jpars_strip _ _ _ Hpar₁ Hpar₂) as Hstrip.
    destruct Hstrip as [Vvcd [Hx HV₂]].
    exists Vvcd.
    split.
    - apply Hx.
    - constructor. apply HV₂.
  + apply IHHpar₁1 in Hpar₂.
    destruct Hpar₂ as [Vvcd₁ [Hy HV₂]].
    apply IHHpar₁2 in Hy.
    destruct Hy as [Vvcd₂ [Hz HVvcd₁]].
    exists Vvcd₂.
    split.
    - apply Hz.
    - constructor 3 with (y := Vvcd₁).
      * apply HV₂.
      * apply HVvcd₁.
}
Qed.

Lemma treds_confluence {S : VSig} (M M₁ M₂ : term S) :
  M →*ₜ M₁ →
  M →*ₜ M₂ →
  ∃ M', M₁ →*ₜ M' ∧ M₂ →*ₜ M'
 with vreds_confluence {S : VSig} (V V₁ V₂ : value S) :
  V →*ᵥ V₁ →
  V →*ᵥ V₂ →
  ∃ V', V₁ →*ᵥ V' ∧ V₂ →*ᵥ V'
 with jreds_confluence {S : VSig} (J J₁ J₂ : jump S) :
  J →*ⱼ J₁ →
  J →*ⱼ J₂ →
  ∃ J', J₁ →*ⱼ J' ∧ J₂ →*ⱼ J'.
Proof.
(* treds_confluence *)
{
  intros Hreds₁ Hreds₂.
  apply treds_pars in Hreds₁.
  apply treds_pars in Hreds₂.
  pose proof (tpars_confluence _ _ _ Hreds₁ Hreds₂) as Hpar_conf.
  destruct Hpar_conf as [M' [HM₁ HM₂]].
  apply tpars_reds in HM₁.
  apply tpars_reds in HM₂.
  exists M'.
  split; assumption.
}
(* vreds_confluence*)
{
  intros Hreds₁ Hreds₂.
  apply vreds_pars in Hreds₁.
  apply vreds_pars in Hreds₂.
  pose proof (vpars_confluence _ _ _ Hreds₁ Hreds₂) as Hpar_conf.
  destruct Hpar_conf as [M' [HM₁ HM₂]].
  apply vpars_reds in HM₁.
  apply vpars_reds in HM₂.
  exists M'.
  split; assumption.
}
(* jreds_confluence *)
{
  intros Hreds₁ Hreds₂.
  apply jreds_pars in Hreds₁.
  apply jreds_pars in Hreds₂.
  pose proof (jpars_confluence _ _ _ Hreds₁ Hreds₂) as Hpar_conf.
  destruct Hpar_conf as [M' [HM₁ HM₂]].
  apply jpars_reds in HM₁.
  apply jpars_reds in HM₂.
  exists M'.
  split; assumption.
}
Qed.