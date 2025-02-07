Require Import Utf8.
Require Import Binding.Lib Binding.Product Binding.Env Binding.Set.
Require Import Syntax.
Require Import String.

Local Open Scope bind_scope.

Inductive ttype :=
  (* propositional atom *)
  | tp_atom   : string → ttype
  | tp_bottom : ttype
  | tp_arrow  : ttype → ttype → ttype.
Inductive ktype :=
  (* type of a continuation (A → ⊥⊥) *)
  | tp_cont   : ttype → ktype.

Record env (A : VSig) := {
  env_v : tv A → ttype;
  env_k : kv A → ktype
}.

Arguments env_v {A}.
Arguments env_k {A}.

Definition empty_env := {|
  env_v := λ (x : tv ⟨∅, ∅⟩), match x with end;
  env_k := λ k, match k with end;
|}.

Definition extend_v {S : VSig} Γ A := {|
  env_v := extend (env_v Γ) A : tv (incV S) → ttype;
  env_k := env_k Γ
|}.
Notation "Γ '↦ᵥ' A" := (extend_v Γ A) (at level 67).

Definition extend_k {S : VSig} (Γ : env S) K := {|
  env_v := env_v Γ : tv (incK S) → ttype;
  env_k := extend (env_k Γ) K;
|}.
Notation "Γ '↦ₖ' K" := (extend_k Γ K) (at level 67).

(* Typing judgement for continuation atoms:
   A is the type M needs to be for q M to be a jump. *)
Reserved Notation "'K[' Γ '⊢' q '∷' A '→⊥⊥' ']'".
Inductive ktyping {S : VSig} (Γ : env S) : katom S → ttype → Prop :=
  | K_Tp :
    (* ----------------------- *)
    K[ Γ ⊢ k_tp ∷ tp_bottom →⊥⊥ ]

  | K_Var : ∀ k A,
    env_k Γ k = tp_cont A →
    (* ------------------ *)
    K[ Γ ⊢ k_var k ∷ A →⊥⊥ ]

where "K[ Γ ⊢ q ∷ A →⊥⊥ ]" := (@ktyping _ Γ q A).

Reserved Notation "'T[' Γ '⊢' M '∷' A  ']'".
Reserved Notation "'J[' Γ '⊢' J '∷' '⊥⊥'  ']'".

Inductive ttyping {S : VSig} (Γ : env S) : term S → ttype → Prop :=
  | T_Var : ∀ x A,
    env_v Γ x = A →
    (* -------------- *)
    T[ Γ ⊢ v_var x ∷ A ]

  | T_App : ∀ M N A B,
    T[ Γ ⊢ M ∷ tp_arrow A B ] →
    T[ Γ ⊢ N ∷ A ] →
    (* ---------------- *)
    T[ Γ ⊢ t_app M N ∷ B ]

  | T_Abs : ∀ M A B,
    T[ Γ ↦ᵥ A ⊢ M ∷ B ] →
    (* ------------------------- *)
    T[ Γ ⊢ v_lam M ∷ tp_arrow A B ]

  | T_Ctrl : ∀ J A,
    J[ Γ ↦ₖ tp_cont A ⊢ J ∷ ⊥⊥ ] →
    (* --------------- *)
    T[ Γ ⊢ t_ctrl J ∷ A ]

with jtyping {S : VSig} (Γ : env S) : jump S → Prop :=
  | J_Tp : ∀ M,
    T[ Γ ⊢ M ∷ tp_bottom ] →
    (* -------------------- *)
    J[ Γ ⊢ j_jmp k_tp M ∷ ⊥⊥ ]

  | J_Cont : ∀ M A k,
    K[ Γ ⊢ k_var k ∷ A →⊥⊥ ] →
    T[ Γ ⊢ M ∷ A ] →
    (* ------------------------- *)
    J[ Γ ⊢ j_jmp (k_var k) M ∷ ⊥⊥ ]

where "T[ Γ ⊢ M ∷ A ]"  := (@ttyping _ Γ M A)
  and "J[ Γ ⊢ J ∷ ⊥⊥ ]" := (@jtyping _ Γ J).

(* Typing judgement for evaluation contexts:
   E will have type A after plugging a term of type B. *)
Reserved Notation "'E[' Γ '⊢' E '∷' A '⇐' B  ']'".
Inductive etyping {S : VSig} (Γ : env S) : ectx S → ttype → ttype → Prop :=
  | E_Hole : ∀ A,
    (* ----------------- *)
    E[ Γ ⊢ e_hole ∷ A ⇐ A ]

  | E_AppL : ∀ E M A B U,
    E[ Γ ⊢ E ∷ tp_arrow A B ⇐ U ] →
    T[ Γ ⊢ M ∷ A ] →
    (* --------------------- *)
    E[ Γ ⊢ e_appl E M ∷ B ⇐ U ]

  | E_AppR : ∀ E (V : value S) A B U,
    T[ Γ ⊢ V ∷ tp_arrow A B ] →
    E[ Γ ⊢ E ∷ A ⇐ U ] →
    (* --------------------- *)
    E[ Γ ⊢ e_appr V E ∷ B ⇐ U ]

where "E[ Γ ⊢ E ∷ A ⇐ B ]" := (@etyping _ Γ E A B).

Lemma etyping_correct {S : VSig} (Γ : env S) E M A B :
  E[ Γ ⊢ E ∷ A ⇐ B ] →
  T[ Γ ⊢ M ∷ B ] →
  T[ Γ ⊢ eplug E M ∷ A ].
Proof.
  intros HE HM.
  induction HE.
  + simpl. apply HM.
  + simpl. econstructor.
    - apply IHHE. apply HM.
    - apply H.
  + simpl. econstructor.
    - apply H.
    - apply IHHE. apply HM.
Qed.

(* ========================================================================= *)
(* fmap, weakening lemmas *)

(* φ is a renaming that preserves types between Γ and Δ. *)
Definition env_map_equiv {A B : VSig} (φ : @prod_arr _ _ Arr Arr A B) (Γ : env A) (Δ : env B) :=
  (∀ x, env_v Δ (arr₁ φ x) = env_v Γ x)
  ∧ (∀ k, env_k Δ (arr₂ φ k) = env_k Γ k).

Lemma env_map_equiv_tv_extend {S T : VSig} (φ : prod_arr S T) Γ Δ A :
  env_map_equiv φ Γ Δ → env_map_equiv (φ ↑) (Γ ↦ᵥ A) (Δ ↦ᵥ A).
Proof.
  intro Hφ.
  split.
  - destruct x as [| x].
    * simpl. reflexivity.
    * simpl. apply Hφ.
  - intros k. simpl. apply Hφ.
Qed.

Lemma env_map_equiv_kv_extend {S T : VSig} (φ : prod_arr S T) Γ Δ A :
  env_map_equiv φ Γ Δ → env_map_equiv (φ ↑) (Γ ↦ₖ A) (Δ ↦ₖ A).
Proof.
  intro Hφ.
  split.
  - intro x. simpl. apply Hφ.
  - destruct k as [| k].
    * simpl. reflexivity.
    * simpl. apply Hφ.
Qed.

(* --------------------------------- *)

Lemma ktyping_fmap {S T : VSig} (φ : prod_arr S T) (Γ : env S) (Δ : env T) q A :
  env_map_equiv φ Γ Δ →
  K[ Γ ⊢ q ∷ A →⊥⊥ ] → K[ Δ ⊢ fmap φ q ∷ A →⊥⊥ ].
Proof.
  intros Hφ Hq.
  destruct Hq.
  + constructor.
  + constructor. rewrite (proj2 Hφ). apply H.
Qed.

Lemma ktyping_fmap2 {S T : VSig} (φ : prod_arr S T) (Γ : env S) (Δ : env T) q A :
  env_map_equiv φ Γ Δ →
  K[ Δ ⊢ fmap φ q ∷ A →⊥⊥ ] → K[ Γ ⊢ q ∷ A →⊥⊥ ].
Proof.
  intros Hφ Hq.
  destruct q.
  + inversion Hq as [| ? ? Hk ]; subst.
    constructor. rewrite <- (proj2 Hφ). apply Hk.
  + inversion Hq; subst.
    constructor.
Qed.

Lemma ktyping_tv_weaken {S : VSig} (Γ : env S) (q : katom S) A B :
  K[ Γ ⊢ q ∷ A →⊥⊥ ] ↔ K[ Γ ↦ᵥ B ⊢ shift q ∷ A →⊥⊥ ].
Proof.
  split.
  + apply ktyping_fmap. split; reflexivity.
  + apply ktyping_fmap2. split; reflexivity.
Qed.

Lemma ktyping_kv_weaken {S : VSig} (Γ : env S) (q : katom S) A B :
  K[ Γ ⊢ q ∷ A →⊥⊥ ] ↔ K[ Γ ↦ₖ B ⊢ shift q ∷ A →⊥⊥ ].
Proof.
  split.
  + apply ktyping_fmap. split; reflexivity.
  + apply ktyping_fmap2. split; reflexivity.
Qed.

(* --------------------------------- *)

Lemma ttyping_fmap {S T : VSig} (φ : prod_arr S T) (Γ : env S) (Δ : env T) M A :
  env_map_equiv φ Γ Δ →
  T[ Γ ⊢ M ∷ A ] → T[ Δ ⊢ fmap φ M ∷ A ]
with jtyping_fmap {S T : VSig} (φ : prod_arr S T) (Γ : env S) (Δ : env T) J :
  env_map_equiv φ Γ Δ →
  J[ Γ ⊢ J ∷ ⊥⊥ ] → J[ Δ ⊢ fmap φ J ∷ ⊥⊥ ].
Proof.
(* ttyping_fmap *)
{
  intros Hφ HM.
  generalize dependent Δ.
  generalize dependent T.
  induction HM; intros T φ Δ Hφ.
  + term_simpl. constructor. subst. apply Hφ.
  + term_simpl. econstructor.
    - apply IHHM1. apply Hφ.
    - apply IHHM2. apply Hφ.
  + term_simpl. constructor.
    apply IHHM. simpl. unfold env_map_equiv. split.
    - destruct x.
      * simpl. reflexivity.
      * simpl. apply Hφ.
    - intro k. simpl. apply Hφ.
  + term_simpl. constructor.
    apply jtyping_fmap with (Γ := Γ ↦ₖ tp_cont A).
    ++ split.
      - intro x. simpl. apply Hφ.
      - destruct k as [| k].
        * simpl. reflexivity.
        * simpl. apply Hφ.
    ++ apply H.
}
(* jtyping_fmap *)
{
  intros Hφ HJ.
  destruct HJ.
  + term_simpl. constructor. apply ttyping_fmap with (Γ := Γ).
    - apply Hφ.
    - apply H.
  + econstructor.
    - apply ktyping_fmap with (Γ := Γ) (q := k_var k).
      * apply Hφ.
      * apply H.
    - apply ttyping_fmap with (Γ := Γ).
      * apply Hφ.
      * apply H0.
}
Qed.

Lemma ttyping_fmap2 {S T : VSig} (φ : prod_arr S T) (Γ : env S) (Δ : env T) M A :
  env_map_equiv φ Γ Δ →
  T[ Δ ⊢ fmap φ M ∷ A ] → T[ Γ ⊢ M ∷ A ]
with value_fmap2 {S T : VSig} (φ : prod_arr S T) (Γ : env S) (Δ : env T) (V : value S) A :
  env_map_equiv φ Γ Δ →
  T[ Δ ⊢ vmap φ V ∷ A ] → T[ Γ ⊢ V ∷ A ]
with jtyping_fmap2 {S T : VSig} (φ : prod_arr S T) (Γ : env S) (Δ : env T) J :
  env_map_equiv φ Γ Δ →
  J[ Δ ⊢ fmap φ J ∷ ⊥⊥ ] → J[ Γ ⊢ J ∷ ⊥⊥ ].
Proof.
(* ttyping_fmap2 *)
{
  intros Hφ Hfmap.
  destruct M.
  + eapply value_fmap2; [ apply Hφ | apply Hfmap ].
  + inversion Hfmap; subst.
    econstructor; eauto.
  + inversion Hfmap; subst.
    constructor.
    eapply jtyping_fmap2.
    * eapply env_map_equiv_kv_extend. apply Hφ.
    * apply H0.
}
(* value_fmap2 *)
{
  intros Hφ Hfmap.
  destruct V.
  + inversion Hfmap; subst.
    constructor.
    rewrite <- (proj1 Hφ). reflexivity.
  + inversion Hfmap; subst.
    constructor.
    eapply ttyping_fmap2.
    * eapply env_map_equiv_tv_extend. apply Hφ.
    * apply H0.
}
(* jtyping_fmap2 *)
{
  intros Hφ Hfmap.
  destruct J.
  destruct k.
  + inversion Hfmap; subst.
    econstructor.
    - eapply ktyping_fmap2 with (q := k_var k).
      * apply Hφ.
      * apply H1.
    - eapply ttyping_fmap2.
      * apply Hφ.
      * apply H2.
  + inversion Hfmap; subst.
    constructor.
    eapply ttyping_fmap2.
    * apply Hφ.
    * apply H0.
}
Qed.

Lemma ttyping_tv_weaken {S : VSig} (Γ : env S) M A B :
  T[ Γ ⊢ M ∷ A ] ↔ T[ Γ ↦ᵥ B ⊢ shift M ∷ A ].
Proof.
  split.
  + apply ttyping_fmap. split; reflexivity.
  + apply ttyping_fmap2. split; reflexivity.
Qed.

Lemma ttyping_kv_weaken {S : VSig} (Γ : env S) M A B :
  T[ Γ ⊢ M ∷ A ] ↔ T[ Γ ↦ₖ B ⊢ shift M ∷ A ].
Proof.
  split.
  + apply ttyping_fmap. split; reflexivity.
  + apply ttyping_fmap2. split; reflexivity.
Qed.

Lemma jtyping_kv_weaken {S : VSig} (Γ : env S) J A :
  J[ Γ ⊢ J ∷ ⊥⊥ ] ↔ J[ Γ ↦ₖ A ⊢ shift J ∷ ⊥⊥ ].
Proof.
  split.
  + apply jtyping_fmap. split; reflexivity.
  + apply jtyping_fmap2. split; reflexivity.
Qed.

Lemma jtyping_tv_weaken {S : VSig} (Γ : env S) J A :
  J[ Γ ⊢ J ∷ ⊥⊥ ] ↔ J[ Γ ↦ᵥ A ⊢ shift J ∷ ⊥⊥ ].
Proof.
  split.
  + apply jtyping_fmap. split; reflexivity.
  + apply jtyping_fmap2. split; reflexivity.
Qed.

(* --------------------------------- *)

Lemma etyping_fmap {S T : VSig} (φ : prod_arr S T) (Γ : env S) (Δ : env T) E A B :
  env_map_equiv φ Γ Δ →
  E[ Γ ⊢ E ∷ A ⇐ B ] → E[ Δ ⊢ fmap φ E ∷ A ⇐ B ].
Proof.
  intros Hφ HE.
  induction HE.
  + constructor.
  + term_simpl. econstructor.
    - apply IHHE.
    - apply ttyping_fmap with (Γ := Γ).
      * apply Hφ.
      * apply H.
  + term_simpl. econstructor.
    - apply ttyping_fmap with (Γ := Γ) (M := V).
      * apply Hφ.
      * apply H.
    - apply IHHE.
Qed.

Lemma etyping_tv_weaken {S : VSig} (Γ : env S) E A B C :
  E[ Γ ⊢ E ∷ A ⇐ B ] → E[ Γ ↦ᵥ C ⊢ shift E ∷ A ⇐ B ].
Proof.
  apply etyping_fmap. split; reflexivity.
Qed.

Lemma etyping_kv_weaken {S : VSig} (Γ : env S) E A B C :
  E[ Γ ⊢ E ∷ A ⇐ B ] → E[ Γ ↦ₖ C ⊢ shift E ∷ A ⇐ B ].
Proof.
  apply etyping_fmap. split; reflexivity.
Qed.

(* ========================================================================= *)
(* bind, substitution lemmas *)

(* φ is a substitution that preserves types between Γ and Δ. *)
Definition env_sub_equiv {S T : VSig} (φ : S {→} T) (Γ : env S) (Δ : env T) :=
  (∀ x, T[ Δ ⊢ sub_v φ x ∷ env_v Γ x ])
  ∧ (∀ k A B,
      let (q, E) := sub_k φ k in
      K[ Γ ⊢ k_var k ∷ A →⊥⊥ ] →
      K[ Δ ⊢ q ∷ B →⊥⊥ ] →
      E[ Δ ⊢ E ∷ B ⇐ A ]
    ).

Lemma env_sub_equiv_tv_extend {S T : VSig} (φ : S {→} T) Γ Δ A :
  env_sub_equiv φ Γ Δ → env_sub_equiv (φ ↑) (Γ ↦ᵥ A) (Δ ↦ᵥ A).
Proof.
  intro Hφ.
  unfold env_sub_equiv.
  split.
  - destruct x as [| x].
    * simpl. constructor. simpl. reflexivity.
    * simpl. apply ttyping_tv_weaken with (M := sub_v φ x). apply Hφ.
  - intros k B C. simpl.
    destruct (sub_k φ k) as [q E] eqn:Heqsub. simpl.
    intro Hk.

    destruct Hφ as [Hφᵥ Hφₖ].
    specialize (Hφₖ k B C). rewrite Heqsub in Hφₖ. rename Hφₖ into HE.

    destruct q as [k' |].
    * term_simpl. intro Hk'.
      apply etyping_tv_weaken. apply HE.
      + eapply ktyping_tv_weaken. apply Hk.
      + eapply ktyping_tv_weaken. apply Hk'.
    * term_simpl. intro Htp.
      apply etyping_tv_weaken. apply HE.
      + eapply ktyping_tv_weaken. apply Hk.
      + eapply ktyping_tv_weaken. apply Htp.
Qed.

Lemma env_sub_equiv_kv_extend {S T : VSig} (φ : S {→} T) Γ Δ A :
  env_sub_equiv φ Γ Δ → env_sub_equiv (φ ↑) (Γ ↦ₖ A) (Δ ↦ₖ A).
Proof.
  intro Hφ.
  split.
  - intro x. simpl. apply ttyping_kv_weaken with (M := sub_v φ x). apply Hφ.
  - intros k B C. simpl.
    destruct k as [| k].
    + term_simpl. intros HVZA HVZB.
      inversion HVZA as [| ? ? HA ]; subst.
      inversion HVZB as [| ? ? HB ]; subst.
      simpl in HA, HB. rewrite HA in HB. inversion HB; subst.
      constructor.
    + destruct (sub_k φ k) as [q E] eqn:Heqsub. term_simpl.
      intro Hk.

      destruct Hφ as [Hφᵥ Hφₖ].
      specialize (Hφₖ k B C). rewrite Heqsub in Hφₖ. rename Hφₖ into HE.

      destruct q as [k' |].
      * term_simpl. intro Hk'.
        apply etyping_kv_weaken. apply HE.
        -- eapply ktyping_kv_weaken. apply Hk.
        -- eapply ktyping_kv_weaken. apply Hk'.
      * term_simpl. intro Htp.
        apply etyping_kv_weaken. apply HE.
        -- eapply ktyping_kv_weaken. apply Hk.
        -- eapply ktyping_kv_weaken. apply Htp.
Qed.

Lemma ttyping_bind {S T : VSig} (φ : S {→} T) (Γ : env S) (Δ : env T) M A :
  (env_sub_equiv φ Γ Δ) →
  T[ Γ ⊢ M ∷ A ] → T[ Δ ⊢ bind φ M ∷ A ]
with jtyping_bind {S T : VSig} (φ : S {→} T) (Γ : env S) (Δ : env T) J :
  (env_sub_equiv φ Γ Δ) →
  J[ Γ ⊢ J ∷ ⊥⊥ ] → J[ Δ ⊢ bind φ J ∷ ⊥⊥ ].
Proof.
(* ttyping_bind *)
{
  intros Hφ HM.
  generalize dependent Δ.
  generalize dependent T.
  induction HM; intros T φ Δ Hφ; unfold bind; term_simpl.
  + subst. apply Hφ.
  + econstructor.
    - apply IHHM1. apply Hφ.
    - apply IHHM2. apply Hφ.
  + constructor. apply IHHM.
    apply env_sub_equiv_tv_extend. apply Hφ.
  + constructor. apply jtyping_bind with (Γ := Γ ↦ₖ tp_cont A).
    - apply env_sub_equiv_kv_extend. apply Hφ.
    - apply H.
}
(* jtyping_bind *)
{
  intros Hφ HJ.
  induction HJ; unfold bind; term_simpl.
  + constructor. apply ttyping_bind with (Γ := Γ).
    - apply Hφ.
    - apply H.
  + destruct (sub_k φ k) as [q E] eqn:Hsub.
    pose proof Hφ as [Hφᵥ Hφₖ].

    destruct q as [k' |].
    - destruct (env_k Δ k') as [C] eqn:Heqk'.
      specialize Hφₖ with k A C. rewrite Hsub in Hφₖ. rename Hφₖ into HE.

      assert (Hk' : K[ Δ ⊢ k_var k' ∷ C →⊥⊥ ]) by (constructor; apply Heqk').

      econstructor.
      * apply Hk'.
      * eapply etyping_correct.
        ++ apply HE.
          -- apply H.
          -- apply Hk'.
        ++ apply ttyping_bind with (Γ := Γ).
          -- apply Hφ.
          -- apply H0.
    - specialize Hφₖ with k A tp_bottom as HE; clear Hφₖ. rewrite Hsub in HE.
      constructor. eapply etyping_correct.
      * apply HE.
        ++ apply H.
        ++ constructor.
      * apply ttyping_bind with (Γ := Γ).
        ++ apply Hφ.
        ++ apply H0.
}
Qed.

Lemma ttyping_subst {S : VSig} (Γ : env S) M (V : value S) A B :
  T[ Γ ⊢ V ∷ B ] →
  T[ Γ ↦ᵥ B ⊢ M ∷ A ] →
  T[ Γ ⊢ subst M V ∷ A ].
Proof.
  intros HV HM. unfold subst.
  apply ttyping_bind with (Γ := Γ ↦ᵥ B).
  + split.
    - intro x. simpl.
      destruct x as [| x].
      * simpl. apply HV.
      * simpl. constructor. reflexivity.
    - intros k C D. simpl.
      intros HkC HkD. inversion HkC; subst. inversion HkD; subst.
      simpl in H0. rewrite H0 in H1. inversion H1; subst.
      constructor.
  + apply HM.
Qed.

Lemma jtyping_subst {S : VSig} (Γ : env S) J q E A B :
  J[ Γ ↦ₖ tp_cont A ⊢ J ∷ ⊥⊥ ] →
  E[ Γ ⊢ E ∷ B ⇐ A ] →
  K[ Γ ⊢ q ∷ B →⊥⊥ ] →
  J[ Γ ⊢ subst J (s_sub q E) ∷ ⊥⊥ ].
Proof.
  intros HJ HE Hq.
  apply jtyping_bind with (Γ := Γ ↦ₖ tp_cont A).
  + split.
    - intro x. simpl. constructor. reflexivity.
    - intros k C D. simpl.
      destruct k as [| k].
      * simpl. intro HAC.
        inversion HAC as [| ? ? HAC']; subst. simpl in HAC'.
        inversion HAC'; subst; clear HAC'.

        destruct q as [k' |].
        ++ intro Hk'. inversion Hq as [| ? ? HBk' ]; subst.
           inversion Hk' as [| ? ? HDk']; subst.
           rewrite HDk' in HBk'. inversion HBk'; subst.
           apply HE.
        ++ intro Htp.
           inversion Hq; subst.
           inversion Htp; subst.
           apply HE.
      * simpl. intros HCk HDk.
        inversion HCk as [| ? ? HenvCk]; subst. simpl in HenvCk.
        inversion HDk as [| ? ? HenvDk]; subst.
        rewrite HenvCk in HenvDk. inversion HenvDk; subst.
        constructor.
  + apply HJ.
Qed.

Lemma jtyping_struct_subst {S : VSig} (Γ : env S) J E A B :
  J[ Γ ↦ₖ tp_cont B ⊢ J ∷ ⊥⊥ ] →
  E[ Γ ↦ₖ tp_cont A ⊢ E ∷ A ⇐ B ] →
  J[ Γ ↦ₖ tp_cont A ⊢ struct_subst J E ∷ ⊥⊥ ].
Proof.
  intros HJ HE.
  apply jtyping_bind with (Γ := Γ ↦ₖ tp_cont B).
  + split; term_simpl.
    - intro x. constructor. reflexivity.
    - intros k C D. term_simpl.
      destruct k as [| k].
      * term_simpl. intros HBC HAD.
        inversion HBC as [| ? ? HBC']; subst. simpl in HBC'.
        inversion HAD as [| ? ? HAD']; subst. simpl in HAD'.
        inversion HBC'; subst; clear HBC'.
        inversion HAD'; subst; clear HAD'.
        apply HE.
      * term_simpl. intros HkC HkD.
        inversion HkC as [| ? ? HenvkC]; subst. simpl in HenvkC.
        inversion HkD as [| ? ? HenvkD]; subst. simpl in HenvkD.
        rewrite HenvkC in HenvkD. inversion HenvkD; subst.
        constructor.
  + apply HJ.
Qed.
