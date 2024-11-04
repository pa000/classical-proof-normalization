Require Import Utf8.
Require Import Syntax Typing Semantics.
Require Import Binding.Lib Binding.Product.

Lemma tpreservation {S : VSig} : ∀ Γ (M : term S) N A,
    T[ Γ ⊢ M ∷ A ] →
    M →ₜ N →
    T[ Γ ⊢ N ∷ A ]
with vpreservation {S : VSig} : ∀ Γ (V : value S) V' A,
    T[ Γ ⊢ V ∷ A ] →
    V →ᵥ V' →
    T[ Γ ⊢ V' ∷ A ]
with jpreservation {S : VSig} : ∀ Γ (J : jump S) J',
    J[ Γ ⊢ J ∷ ⊥⊥ ] →
    J →ⱼ J' →
    J[ Γ ⊢ J' ∷ ⊥⊥ ].
Proof.
(* tpreservation *)
{
  intros Γ M N A HM Hred.
  generalize dependent A.
  induction Hred; intros A HT.
  + inversion HT as [| ? ? B ? Hlam HV | |]; subst.
    eapply ttyping_subst.
    - apply HV.
    - inversion Hlam as [| | ? ? ? HM |]; subst. apply HM.
  + inversion HT as [| ? ? B ? Hctrl HN | |]; subst.
    constructor.
    eapply jtyping_struct_subst.
    - inversion Hctrl as [| | | ? ? HJ ]; subst.
      apply HJ.
    - econstructor.
      * constructor.
      * apply ttyping_kv_weaken. apply HN.
  + inversion HT as [| ? ? B ? HV Hctrl | |]; subst.
    constructor.
    eapply jtyping_struct_subst.
    - inversion Hctrl as [| | | ? ? HJ ]; subst.
      apply HJ.
    - econstructor.
      * apply ttyping_kv_weaken with (M := V). apply HV.
      * constructor.
  + inversion HT as [| | | ? ? Hjmp ]; subst.
    inversion Hjmp as [| ? B ? HVZ HM ]; subst.
    simpl in HVZ. inversion HVZ as [| ? ? HAB ]; subst. simpl in HAB.
    inversion HAB; subst.
    apply ttyping_kv_weaken in HM.
    apply HM.
  + eapply vpreservation.
    - apply HT.
    - apply H.
  + inversion HT as [| ? ? B ? HM HN | |]; subst.
    econstructor.
    - eapply tpreservation.
      * apply HM.
      * apply Hred.
    - apply HN.
  + inversion HT as [| ? ? B ? HM HN | |]; subst.
    econstructor.
    - apply HM.
    - eapply tpreservation.
      * apply HN.
      * apply Hred.
  + inversion HT as [| | | ? ? HJ ]; subst.
    constructor.
    eapply jpreservation.
    - apply HJ.
    - apply H.
}
(* vpreservation *)
{
  intros Γ V V' A HT Hred.
  destruct Hred.
  + inversion HT as [| | ? B C HM |]; subst.
    constructor.
    eapply tpreservation.
    - apply HM.
    - apply H.
}
(* jpreservation *)
{
  intros Γ J J' HT Hred.
  destruct Hred.
  + inversion HT as [ ? Hctrl | ? B k Hk Hctrl ]; subst.
    - inversion Hctrl as [| | | ? ? HJ ]; subst.
      eapply jtyping_subst.
      * apply HJ.
      * constructor.
      * constructor.
    - inversion Hctrl as [| | | ? ? HJ ]; subst.
      eapply jtyping_subst.
      * apply HJ.
      * constructor.
      * apply Hk.
  + inversion HT as [ ? HM | ? A k Hk HM ]; subst.
    - constructor.
      eapply tpreservation.
      * apply HM.
      * apply H.
    - econstructor.
      * apply Hk.
      * eapply tpreservation.
        ++ apply HM.
        ++ apply H.
}
Qed.
