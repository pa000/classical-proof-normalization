Require Import Utf8.
Require Import Binding.Lib Binding.Set Binding.Product.

(* We use nested datatype variable binding representation,
   so our terms/values/jumps are parametrized by the set
   of potentially free variables.
   We have two kinds of variables: term variables and continuation variables,
   so we use a product of Sets. *)

Definition VSig := Set × Set.
(* term variables *)
Definition tv (A : VSig) := π₁ A.
(* continuation variables *)
Definition kv (A : VSig) := π₂ A.

Notation incV := (on₁ inc).
Notation incK := (on₂ inc).

(* continuation atoms *)
Inductive katom (A : VSig) : Set :=
  | k_var   : kv A → katom A
  | k_tp    : katom A.

(* We use bidirectionality hints (&) to solve
   problems with unifying `⟨inc A, B⟩` and `incV ⟨A, B⟩`. *)
Arguments k_var   & {A}.
Arguments k_tp    & {A}.

Inductive term (A : VSig) : Set :=
  | t_value : value A → term A
  | t_app   : term A → term A → term A
  | t_ctrl  : jump (incK A) → term A
with value (A : VSig) : Set :=
  | v_var   : tv A → value A
  | v_lam   : term (incV A) → value A
with jump (A : VSig) : Set :=
  | j_jmp   : katom A → term A → jump A.

Coercion t_value : value >-> term.

Arguments t_value & {A}.
Arguments t_app   & {A}.
Arguments t_ctrl  & {A}.

Arguments v_var   & {A}.
Arguments v_lam   & {A}.

Arguments j_jmp   & {A}.

Inductive ectx (A : VSig) : Set :=
  | e_hole : ectx A
  | e_appl : ectx A → term A → ectx A
  | e_appr : value A → ectx A → ectx A.

Arguments e_hole  & {A}.
Arguments e_appl  & {A}.
Arguments e_appr  & {A}.

Fixpoint eplug {A : VSig} (E : ectx A) (t : term A) : term A :=
  match E with
  | e_hole      => t
  | e_appl E t' => t_app (eplug E t) t'
  | e_appr v E  => t_app v (eplug E t)
  end.

(* Composition of evaluation contexts: (ecomp E1 E2)[M] = E1[E2[M]] *)
Fixpoint ecomp {S : VSig} (E1 : ectx S) (E2 : ectx S) : ectx S :=
  match E1 with
  | e_hole      => E2
  | e_appl E1 t => e_appl (ecomp E1 E2) t
  | e_appr v E1 => e_appr v (ecomp E1 E2)
  end.

Lemma ecomp_assoc {S : VSig} (E₁ E₂ E₃ : ectx S) :
  ecomp E₃ (ecomp E₂ E₁) = ecomp (ecomp E₃ E₂) E₁.
Proof.
  induction E₃.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    apply IHE₃.
  + term_simpl. f_equal.
    apply IHE₃.
Qed.

(* We use structural substitution with jumps.
   J[q E/k] means replace every occurence of k N with q E[N] in J. *)
Inductive ssub (A : VSig) : Type :=
  | s_sub : katom A → ectx A → ssub A.

Arguments s_sub & {A}.

(* ========================================================================= *)
(* Mapping, i.e. variable renaming *)

Definition kmap {A B : VSig} (φ : @prod_arr _ _ Arr Arr A B) (q : katom A) : katom B :=
  match q with
  | k_var k => k_var (arr₂ φ k)
  | k_tp    => k_tp
  end.

Instance FMap_katom : FunctorCore katom := @kmap.

Fixpoint tmap {A B : VSig} (φ : prod_arr A B) (t : term A) : term B :=
  match t with
  | t_value v   => vmap φ v
  | t_app t₁ t₂ => t_app (tmap φ t₁) (tmap φ t₂)
  | t_ctrl j    => t_ctrl (jmap (lift φ) j)
  end
with vmap {A B : VSig} (φ : prod_arr A B) (v : value A) : value B :=
  match v with
  | v_var x => v_var (arr₁ φ x)
  | v_lam t => v_lam (tmap (lift φ) t)
  end
with jmap {A B : VSig} (φ : prod_arr A B) (j : jump A) : jump B :=
  match j with
  | j_jmp q t => j_jmp (kmap φ q) (tmap φ t)
  end.

Instance FMap_term  : FunctorCore term  := @tmap.
Instance FMap_value : FunctorCore value := @vmap.
Instance FMap_jump  : FunctorCore jump  := @jmap.

Local Open Scope bind_scope.

Lemma tmap_id {A : VSig} (φ : prod_arr A A) M (EQ : φ ≡ ı) : tmap φ M = M
with  vmap_id {A : VSig} (φ : prod_arr A A) V (EQ : φ ≡ ı) : vmap φ V = V
with  jmap_id {A : VSig} (φ : prod_arr A A) J (EQ : φ ≡ ı) : jmap φ J = J.
Proof.
(* tmap_id *)
{
  induction M as [? V | ? M₁ IHM₁ M₂ | ? J ].
  + term_simpl. f_equal. apply vmap_id. apply EQ.
  + term_simpl. f_equal.
    - apply IHM₁. apply EQ.
    - apply IHM₂. apply EQ.
  + term_simpl. f_equal.
    apply jmap_id.
    apply lift_id.
    apply EQ.
}
(* vmap_id *)
{
  induction V as [x | M].
  + term_simpl. f_equal. apply EQ.
  + term_simpl. f_equal.
    apply tmap_id.
    apply lift_id.
    apply EQ.
}
(* jmap_id *)
{
  induction J as [q M].
  + term_simpl. f_equal.
    - destruct q.
      * term_simpl. f_equal. apply EQ.
      * term_simpl. reflexivity.
    - apply tmap_id. apply EQ.
}
Qed.

Lemma tmap_map_comp {S T U : VSig} (φ₂ : prod_arr T U) (φ₁ : prod_arr S T) φ M (EQ : φ₂ ∘ φ₁ ≡ φ) :
  tmap φ₂ (fmap φ₁ M) = fmap φ M
with vmap_map_comp {S T U : VSig} (φ₂ : prod_arr T U) (φ₁ : prod_arr S T) φ V (EQ : φ₂ ∘ φ₁ ≡ φ) :
  vmap φ₂ (fmap φ₁ V) = fmap φ V
with jmap_map_comp {S T U : VSig} (φ₂ : prod_arr T U) (φ₁ : prod_arr S T) φ J (EQ : φ₂ ∘ φ₁ ≡ φ) :
  jmap φ₂ (fmap φ₁ J) = fmap φ J.
Proof.
(* tmap_map_comp *)
{
  induction M as [? V | ? M₁ IHM₁ M₂ | ? J].
  + term_simpl. f_equal. apply vmap_map_comp. apply EQ.
  + term_simpl. f_equal.
    - apply IHM₁. apply EQ.
    - apply IHM₂. apply EQ.
  + term_simpl. f_equal.
    apply jmap_map_comp.
    apply lift_comp.
    apply EQ.
}
(* vmap_map_comp *)
{
  induction V as [x | M].
  + term_simpl. f_equal. apply EQ.
  + term_simpl. f_equal.
    apply tmap_map_comp.
    apply lift_comp.
    apply EQ.
}
(* jmap_map_comp *)
{
  induction J as [q M].
  + term_simpl. f_equal.
    - destruct q as [k |].
      * term_simpl. f_equal. apply EQ.
      * term_simpl. reflexivity.
    - apply tmap_map_comp.
      apply EQ.
}
Qed.

Instance Functor_term  : Functor term  := {| map_id := @tmap_id; map_map_comp := @tmap_map_comp |}.
Instance Functor_value : Functor value := {| map_id := @vmap_id; map_map_comp := @vmap_map_comp |}.
Instance Functor_jump  : Functor jump  := {| map_id := @jmap_id; map_map_comp := @jmap_map_comp |}.

Fixpoint emap {A B : VSig} (φ : prod_arr A B) (E : ectx A) : ectx B :=
  match E with
  | e_hole     => e_hole
  | e_appl E t => e_appl (emap φ E) (tmap φ t)
  | e_appr v E => e_appr (vmap φ v) (emap φ E)
  end.

Instance FMap_ectx : FunctorCore ectx := @emap.

Lemma emap_id {A : VSig} (φ : prod_arr A A) E (EQ : φ ≡ ı) : emap φ E = E.
Proof.
  induction E; term_simpl; f_equal; try apply map_id; assumption.
Qed.

Lemma emap_map_comp {S T U : VSig} (φ₂ : prod_arr T U) (φ₁ : prod_arr S T) φ E (EQ : φ₂ ∘ φ₁ ≡ φ) :
  emap φ₂ (fmap φ₁ E) = fmap φ E.
Proof.
  induction E; term_simpl; f_equal; try apply map_map_comp; assumption.
Qed.

Instance Functor_etcx : Functor ectx := {| map_id := @emap_id; map_map_comp := @emap_map_comp |}.

Lemma emap_plug_comm {S T : VSig} (E : ectx S) (M : term S) (φ : prod_arr S T) :
  fmap φ (eplug E M) = eplug (fmap φ E) (fmap φ M).
Proof.
  induction E; term_simpl; f_equal; assumption.
Qed.

Lemma ecomp_pure {S : VSig} (E : ectx S) :
  ecomp E e_hole = E.
Proof.
  induction E; term_simpl; f_equal; assumption.
Qed.

Definition smap {A B : VSig} (φ : prod_arr A B) (s : ssub A) : ssub B :=
  match s with
  | s_sub q E => s_sub (kmap φ q) (emap φ E)
  end.

Instance FMap_ssub : FunctorCore ssub := @smap.

(* ========================================================================= *)
(* Binding, i.e. simultaneous subsitution *)

Record VSub (A B : VSig) : Type :=
  { sub_v : tv A → value B
  ; sub_k : kv A → ssub B
  }.

Arguments sub_v {A B}.
Arguments sub_k {A B}.

Notation "A '{→}' B" := (VSub A B) (at level 50).

Instance LiftableCore_sub_incV : LiftableCore VSub incV :=
  { lift := λ A B (φ : A {→} B),
      {|
        sub_v := λ (x : tv (incV A)),
          match x with
          | VZ => v_var (VZ : tv (incV B))
          | VS y => shift (sub_v φ y)
          end
      ;  sub_k := λ k, shift (sub_k φ k)
      |}
  }.

Instance LiftableCore_sub_incK : LiftableCore VSub incK :=
  { lift := λ A B (φ : A {→} B),
      {|
        sub_v := λ (x : tv (incK A)), shift (sub_v φ x) : value (incK B)
      ; sub_k := λ (k : kv (incK A)),
          match k with
          | VZ   => s_sub (k_var VZ) e_hole
          | VS c => shift (sub_k φ c)
          end
      |}
  }.

Fixpoint tbind {A B : VSig} (φ : A {→} B) (t : term A) : term B :=
  match t with
  | t_value v   => vbind φ v
  | t_app t₁ t₂ => t_app (tbind φ t₁) (tbind φ t₂)
  | t_ctrl j    => t_ctrl (jbind (lift φ) j)
  end
with vbind {A B : VSig} (φ : A {→} B) (v : value A) : value B :=
  match v with
  | v_var x => sub_v φ x
  | v_lam t => v_lam (tbind (lift φ) t)
  end
with jbind {A B : VSig} (φ : A {→} B) (j : jump A) : jump B :=
  match j with
  | j_jmp (k_var k) t =>
    let (q, E) := (sub_k φ k) in j_jmp q (eplug E (tbind φ t))
  | j_jmp k_tp t => j_jmp k_tp (tbind φ t)
  end.

Instance BindCore_term  : BindCore term  := @tbind.
Instance BindCore_value : BindCore value := @vbind.
Instance BindCore_jump  : BindCore jump  := @jbind.

Fixpoint ebind {A B : VSig} (φ : A {→} B) (E : ectx A) : ectx B :=
  match E with
  | e_hole     => e_hole
  | e_appl E t => e_appl (ebind φ E) (tbind φ t)
  | e_appr v E => e_appr (vbind φ v) (ebind φ E)
  end.

Instance BindCore_ectx : BindCore ectx := @ebind.

Definition sbind {A B : VSig} (φ : A {→} B) (s : ssub A) : ssub B :=
  match s with
  | s_sub (k_var k) E =>
    let (q, E') := sub_k φ k in s_sub q (ecomp E' (ebind φ E))
  | s_sub k_tp E => s_sub k_tp (ebind φ E)
  end.

Instance BindCore_ssub : BindCore ssub := @sbind.

Instance EqIndCore_VSub : EqIndCore VSub :=
  {
    equal := λ S T φ ψ,
      (∀ x, sub_v φ x = sub_v ψ x)
      ∧ (∀ k, sub_k φ k = sub_k ψ k)
  }.

Instance ArrowCore_VSub : ArrowCore VSub :=
  {
    arrow_id := λ S,
      {|
        sub_v := λ x, v_var x
      ; sub_k := λ k, s_sub (k_var k) e_hole
      |}
  ; arrow_comp := λ A B C ψ φ,
      {|
        sub_v := λ (x : tv A), bind ψ (sub_v φ x)
      ; sub_k := λ k,
          let (q',  E2) := sub_k φ k in
          match q' with
          | k_tp     => s_sub k_tp (bind ψ E2)
          | k_var k' =>
            let (q'', E1) := sub_k ψ k' in
            s_sub q'' (ecomp E1 (bind ψ E2))
          end
      |}
  }.

Definition struct_sub {A : VSig} E := {|
    sub_v := λ v, v_var v : value (incK A)
  ; sub_k := λ k,
      match k with
      | VZ   => s_sub (k_var VZ) E
      | VS y => s_sub (k_var (VS y)) e_hole
      end
  |}.

Definition struct_subst {A : VSig} (j : jump (incK A)) (E : ectx (incK A)) : jump (incK A) :=
  bind (struct_sub E) j.

Instance SubstitutableCore_value : SubstitutableCore VSub value incV :=
  { mk_subst := λ A v,
    {|
      sub_v := λ (x : tv (incV A)),
        match x with
        | VZ   => v
        | VS y => v_var y
        end
    ; sub_k := λ k, s_sub (k_var k) e_hole
    |}
  }.

Instance SubstitutableCore_jump : SubstitutableCore VSub ssub incK :=
  { mk_subst := λ A qE,
    {|
      sub_k := λ k,
        match k with
        | VZ   => qE
        | VS y => s_sub (k_var y) e_hole
        end
    ; sub_v := λ (x : tv (incK A)), v_var x : value A
    |}
  }.

Instance SubstCore_prod_arr_VSub : SubstCore prod_arr VSub :=
  {
    subst_of_arr := λ A B (φ : @prod_arr _ _ Arr Arr A B),
      {|
        sub_v := λ x, v_var (arr₁ φ x)
      ; sub_k := λ k, s_sub (k_var (arr₂ φ k)) e_hole
      |}
  }.

Program Instance EqInd_VSub : EqInd VSub.
Next Obligation.
  constructor.
  + constructor.
    - reflexivity.
    - reflexivity.
  + constructor.
    rename x into φ₁, y into φ₂.
    - intro x. symmetry. apply H.
    - intro k. symmetry. apply H.
  + constructor;
    rename x into φ₁, y into φ₂, z into φ₃, H into Hφ₁φ₂, H0 into Hφ₂φ₃.
    - intro x. etransitivity.
      * apply Hφ₁φ₂.
      * apply Hφ₂φ₃.
    - intro k. etransitivity.
      * apply Hφ₁φ₂.
      * apply Hφ₂φ₃.
Qed.

Program Instance ASLiftInj_prod_arr_VSub_incK : ASLiftInj prod_arr VSub incK.
Next Obligation.
  constructor;
  destruct EQ as [EQᵥ EQₖ].
  + intro x.
    specialize EQᵥ with x.
    term_simpl in EQᵥ.

    term_simpl. rewrite <- EQᵥ. term_simpl. reflexivity.
  + intro k.
    destruct k as [| k].
    - term_simpl. reflexivity.
    - term_simpl.
      specialize EQₖ with k. term_simpl in EQₖ.
      rewrite <- EQₖ.
      term_simpl. reflexivity.
Qed.

Program Instance ASLiftInj_prod_arr_VSub_incV : ASLiftInj prod_arr VSub incV.
Next Obligation.
  constructor;
  destruct EQ as [EQᵥ EQₖ].
  + intro x.
    destruct x as [| x].
    - term_simpl. reflexivity.
    - specialize EQᵥ with x.
      term_simpl in EQᵥ.

      term_simpl. rewrite <- EQᵥ. term_simpl. reflexivity.
  + intro k.
    specialize EQₖ with k. term_simpl in EQₖ.

    term_simpl.
    rewrite <- EQₖ.
    term_simpl. reflexivity.
Qed.

Lemma tbind_map {S T : VSig} (φ : prod_arr S T) ψ (M : term S) (EQ : φ ̂ ≡ ψ) :
  fmap φ M = bind ψ M
 with vbind_map {S T : VSig} (φ : prod_arr S T) ψ (V : value S) (EQ : φ ̂ ≡ ψ) :
  fmap φ V = bind ψ V
 with jbind_map {S T : VSig} (φ : prod_arr S T) ψ (J : jump S) (EQ : φ ̂ ≡ ψ) :
  fmap φ J = bind ψ J.
Proof.
(* tbind_map *)
{
  induction M.
  + term_simpl. f_equal. apply vbind_map. apply EQ.
  + term_simpl. f_equal.
    - apply IHM1. apply EQ.
    - apply IHM2. apply EQ.
  + term_simpl. f_equal.
    apply jbind_map.
    apply lift_of.
    apply EQ.
}
(* vbind_map *)
{
  induction V.
  + term_simpl. apply EQ.
  + term_simpl. f_equal.
    apply tbind_map.
    apply lift_of.
    apply EQ.
}
(* jbind_map *)
{
  pose proof EQ as [_ EQₖ].

  induction J.
  + term_simpl.
    destruct k.
    - specialize EQₖ with k.
      rewrite <- EQₖ.
      term_simpl. f_equal.
      apply tbind_map.
      apply EQ.
    - term_simpl. f_equal.
      apply tbind_map.
      apply EQ.
}
Qed.

Instance BindMapPure_term  : BindMapPure term  := { bind_map := @tbind_map }.
Instance BindMapPure_value : BindMapPure value := { bind_map := @vbind_map }.
Instance BindMapPure_jump  : BindMapPure jump  := { bind_map := @jbind_map }.

Lemma ebind_map {S T : VSig} (φ : prod_arr S T) ψ (E : ectx S) (EQ : φ ̂ ≡ ψ) :
  fmap φ E = bind ψ E.
Proof.
  induction E.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    - apply IHE.
    - apply tbind_map. apply EQ.
  + term_simpl. f_equal.
    - apply vbind_map. apply EQ.
    - apply IHE.
Qed.

Instance BindMapPure_ectx : BindMapPure ectx := { bind_map := @ebind_map }.

Lemma ecomp_fmap {S T : VSig} (E1 : ectx S) (E2 : ectx S) (φ : prod_arr S T) :
  ecomp (fmap φ E1) (fmap φ E2) = fmap φ (ecomp E1 E2).
Proof.
  induction E1.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    apply IHE1.
  + term_simpl. f_equal.
    apply IHE1.
Qed.

Lemma ecomp_kshift {S : VSig} (E1 : ectx S) (E2 : ectx S) :
  ecomp (shift E1) (shift E2) = shift (ecomp E1 E2).
Proof.
  apply ecomp_fmap.
Qed.

Lemma ecomp_vshift {S : VSig} (E1 : ectx S) (E2 : ectx S) :
  ecomp (shift (Inc := incV) E1) (shift E2) = fmap mk_shift (ecomp E1 E2).
Proof.
  apply ecomp_fmap.
Qed.

Program Instance ASLiftComm_prod_arr_VSub_incK : ASLiftComm prod_arr VSub incK.
Next Obligation.
  term_simpl.
  destruct EQ as [EQᵥ EQₖ]. simpl in EQₖ, EQᵥ.

  constructor.
  + intro x. term_simpl.
    rewrite <- map_to_bind.
    term_simpl. unfold shift. f_equal.

    specialize EQᵥ with x. term_simpl in EQᵥ. rewrite <- map_to_bind in EQᵥ.

    apply EQᵥ.
  + intro k.
    destruct k as [| k].
    - term_simpl. reflexivity.
    - term_simpl. specialize EQₖ with k.
      destruct (sub_k g₂ (arr₂ f₂ k)) as [q₁ E₁].
      destruct (sub_k g₁ k) as [q₂ E₂].
      term_simpl.

      apply (f_equal shift) in EQₖ.
      term_simpl in EQₖ.
      rewrite <- ecomp_kshift in EQₖ.
      rewrite <- map_to_bind in EQₖ.
      term_simpl in EQₖ.

      rewrite <- map_to_bind.
      rewrite fmap_liftA_shift_comm.

      rewrite EQₖ.
      destruct q₂; reflexivity.
Qed.

Program Instance ASLiftComm_prod_arr_VSub_incV : ASLiftComm prod_arr VSub incV.
Next Obligation.
  term_simpl.
  destruct EQ as [EQᵥ EQₖ]. simpl in EQₖ, EQᵥ.

  constructor.
  + intro x. term_simpl.
    destruct x as [| x].
    - term_simpl. reflexivity.
    - rewrite <- map_to_bind.
      term_simpl. unfold shift. f_equal.

      specialize EQᵥ with x. term_simpl in EQᵥ. rewrite <- map_to_bind in EQᵥ.

      apply EQᵥ.
  + intro k.
    term_simpl. specialize EQₖ with k.
    destruct (sub_k g₂ (arr₂ f₂ k)) as [q₁ E₁].
    destruct (sub_k g₁ k) as [q₂ E₂].
    term_simpl.

    apply (f_equal (shift (Inc := incV))) in EQₖ.
    term_simpl in EQₖ.
    rewrite <- ecomp_vshift in EQₖ.
    rewrite <- map_to_bind in EQₖ.
    term_simpl in EQₖ.

    rewrite <- map_to_bind.
    rewrite fmap_liftA_shift_comm.

    destruct q₂; apply EQₖ.
Qed.

Lemma tbind_map_comm {S T₁ T₂ U : VSig} (φ₁ : prod_arr T₁ U) (φ₂ : prod_arr S T₂) (ψ₁ : S {→} T₁) ψ₂ (M : term S) (EQ : ψ₂ ∘ φ₂ ̂ ≡ φ₁ ̂ ∘ ψ₁) :
  bind ψ₂ (fmap φ₂ M) = fmap φ₁ (bind ψ₁ M)
 with vbind_map_comm {S T₁ T₂ U : VSig} (φ₁ : prod_arr T₁ U) (φ₂ : prod_arr S T₂) (ψ₁ : S {→} T₁) ψ₂ (V : value S) (EQ : ψ₂ ∘ φ₂ ̂ ≡ φ₁ ̂ ∘ ψ₁) :
  bind ψ₂ (fmap φ₂ V) = fmap φ₁ (bind ψ₁ V)
 with jbind_map_comm {S T₁ T₂ U : VSig} (φ₁ : prod_arr T₁ U) (φ₂ : prod_arr S T₂) (ψ₁ : S {→} T₁) ψ₂ (J : jump S) (EQ : ψ₂ ∘ φ₂ ̂ ≡ φ₁ ̂ ∘ ψ₁) :
  bind ψ₂ (fmap φ₂ J) = fmap φ₁ (bind ψ₁ J).
Proof.
(* tbind_map_comm *)
{
  induction M.
  + term_simpl. f_equal. apply vbind_map_comm. apply EQ.
  + term_simpl. f_equal.
    - apply IHM1. apply EQ.
    - apply IHM2. apply EQ.
  + term_simpl. f_equal.
    apply jbind_map_comm.
    apply lift_comm.
    apply EQ.
}
(* vbind_map_comm *)
{
  induction V.
  + term_simpl.
    destruct EQ as [EQ _]. specialize EQ with t.
    term_simpl in EQ.
    rewrite <- map_to_bind in EQ.
    apply EQ.
  + term_simpl. f_equal.
    apply tbind_map_comm.
    apply lift_comm.
    apply EQ.
}
(* jbind_map_comm *)
{
  induction J as [q M].

  + term_simpl.
    destruct q as [k |].
    - term_simpl.
      pose proof EQ as [_ EQₖ]. specialize EQₖ with k.
      term_simpl in EQₖ.

      destruct (sub_k ψ₁ k) as [q E].
      destruct (sub_k ψ₂ (arr₂ φ₂ k)) as [q' E'].

      replace (BindCore_ectx T₁ U (φ₁ ̂) E) with (bind (φ₁ ̂) E) in EQₖ by reflexivity.
      rewrite <- map_to_bind in EQₖ.
      destruct q as [k' |].
      * term_simpl. inversion EQₖ as [[Hq' HE']]. f_equal.
        rewrite emap_plug_comm. f_equal.
        ** rewrite ecomp_pure in HE'.
           apply HE'.
        ** apply tbind_map_comm.
           apply EQ.
      * term_simpl. inversion EQₖ as [[Hq' HE']]. f_equal.
        rewrite emap_plug_comm. f_equal.
        ** rewrite ecomp_pure in HE'.
           apply HE'.
        ** apply tbind_map_comm.
           apply EQ.
    - term_simpl. f_equal.
      apply tbind_map_comm.
      apply EQ.
}
Qed.

Instance BindMapComm_term  : BindMapComm term  := { bind_map_comm := @tbind_map_comm }.
Instance BindMapComm_value : BindMapComm value := { bind_map_comm := @vbind_map_comm }.
Instance BindMapComm_jump  : BindMapComm jump  := { bind_map_comm := @jbind_map_comm }.

Lemma ebind_map_comm {S T₁ T₂ U : VSig} (φ₁ : prod_arr T₁ U) (φ₂ : prod_arr S T₂) (ψ₁ : S {→} T₁) ψ₂ (E : ectx S) (EQ : ψ₂ ∘ φ₂ ̂ ≡ φ₁ ̂ ∘ ψ₁) :
  bind ψ₂ (fmap φ₂ E) = fmap φ₁ (bind ψ₁ E).
Proof.
  induction E.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    - apply IHE.
    - apply tbind_map_comm. apply EQ.
  + term_simpl. f_equal.
    - apply vbind_map_comm. apply EQ.
    - apply IHE.
Qed.

Instance BindMapComm_ectx : BindMapComm ectx := { bind_map_comm := @ebind_map_comm }.

Program Instance SubstFMap_prod_arr_VSub_value_incV : SubstFMap prod_arr VSub value incV.
Next Obligation.
  constructor.
  + intro x. term_simpl.
    destruct x.
    - term_simpl.
      rewrite <- map_to_bind.
      reflexivity.
    - term_simpl.
      reflexivity.
  + intro k. term_simpl. reflexivity.
Qed.

Program Instance SubstFMap_prod_arr_VSub_ssub_incK : SubstFMap prod_arr VSub ssub incK.
Next Obligation.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k.
    destruct k.
    - term_simpl.
      destruct v as [q E].
      destruct q as [k |].
      * term_simpl.
        rewrite ecomp_pure.
        rewrite <- map_to_bind.
        reflexivity.
      * term_simpl.
        rewrite ecomp_pure.
        rewrite <- map_to_bind.
        reflexivity.
    - term_simpl. reflexivity.
Qed.

Program Instance LiftSShift_prod_arr_VSub_incK : LiftSShift prod_arr VSub incK.
Next Obligation.
  constructor.
  + intro x. term_simpl.
    rewrite <- map_to_bind. reflexivity.
  + intro k. term_simpl.
    destruct (sub_k f k) as [q E].
    term_simpl. destruct q as [k' |].
    - term_simpl.
      rewrite ecomp_pure.
      rewrite <- map_to_bind.
      reflexivity.
    - term_simpl.
      rewrite ecomp_pure.
      rewrite <- map_to_bind.
      reflexivity.
Qed.

Program Instance LiftSShift_prod_arr_VSub_incV : LiftSShift prod_arr VSub incV.
Next Obligation.
  constructor.
  + intro x. term_simpl.
    rewrite <- map_to_bind. reflexivity.
  + intro k. term_simpl.
    destruct (sub_k f k) as [q E].
    term_simpl. destruct q as [k' |].
    - term_simpl.
      rewrite ecomp_pure.
      rewrite <- map_to_bind.
      reflexivity.
    - term_simpl.
      rewrite ecomp_pure.
      rewrite <- map_to_bind.
      reflexivity.
Qed.

Program Instance Liftable_VSub_incK : Liftable VSub incK.
Next Obligation.
  pose proof EQ as [EQᵥ EQₖ].
  term_simpl in EQᵥ.
  term_simpl in EQₖ.
  constructor.
  + intro x. term_simpl.
    specialize EQᵥ with x. term_simpl in EQᵥ.
    apply (f_equal shift) in EQᵥ. apply EQᵥ.
  + intro k. destruct k as [| k].
    - term_simpl. reflexivity.
    - term_simpl. specialize EQₖ with k.
      apply (f_equal shift) in EQₖ. apply EQₖ.
Qed.
Next Obligation.
  pose proof EQ as [EQᵥ EQₖ]; term_simpl in EQᵥ; term_simpl in EQₖ;
  term_simpl; term_simpl in EQ.
  constructor.
  + clear EQₖ. intro x. term_simpl.
    specialize EQᵥ with x. term_simpl in EQᵥ.
    f_equal. apply EQᵥ.
  + clear EQᵥ. intro k. destruct k.
    - term_simpl. reflexivity.
    - term_simpl. specialize EQₖ with π.
      destruct (sub_k g π) as [q E]. term_simpl.
      destruct q as [k |].
      * term_simpl. destruct (sub_k f k) as [q' E']. term_simpl.
        rewrite ecomp_kshift.
        replace (s_sub (shift q') (shift (ecomp E' (bind f E))))
           with (shift (s_sub q' (ecomp E' (bind f E)))) by reflexivity.
        f_equal.
        apply EQₖ.
      * term_simpl.
        replace (s_sub k_tp (shift (bind f E)))
           with (shift (s_sub k_tp (bind f E))) by reflexivity.
        f_equal.
        apply EQₖ.
Qed.
Next Obligation.
  constructor.
  rename x into φ, y into ψ.
  + intro x. term_simpl. f_equal. apply H.
  + intro k. destruct k.
    - term_simpl. reflexivity.
    - term_simpl. f_equal. apply H.
Qed.

Program Instance Liftable_VSub_incV : Liftable VSub incV.
Next Obligation.
  pose proof EQ as [EQᵥ EQₖ].
  term_simpl in EQᵥ.
  term_simpl in EQₖ.
  constructor.
  + intro x. destruct x as [| x].
    - term_simpl. reflexivity.
    - term_simpl. specialize EQᵥ with x. term_simpl in EQᵥ.
      apply (f_equal (shift (Inc := incV))) in EQᵥ. apply EQᵥ.
  + intro k. term_simpl.
    term_simpl. specialize EQₖ with k.
    apply (f_equal (shift (Inc := incV))) in EQₖ. apply EQₖ.
Qed.
Next Obligation.
  pose proof EQ as [EQᵥ EQₖ]; term_simpl in EQᵥ; term_simpl in EQₖ;
  term_simpl; term_simpl in EQ.
  constructor.
  + clear EQₖ. intro x. destruct x as [| x].
    - term_simpl. reflexivity.
    - term_simpl. specialize EQᵥ with x. term_simpl in EQᵥ.
      f_equal. apply EQᵥ.
  + clear EQᵥ. intro k. 
    term_simpl. specialize EQₖ with k.
    destruct (sub_k g k) as [q E]. term_simpl.
    destruct q as [k' |].
    * term_simpl. destruct (sub_k f k') as [q' E']. term_simpl.
      rewrite ecomp_vshift.
      apply (f_equal (shift (Inc := incV))) in EQₖ.
      apply EQₖ.
    * term_simpl.
      apply (f_equal (shift (Inc := incV))) in EQₖ.
      apply EQₖ.
Qed.
Next Obligation.
  constructor.
  rename x into φ, y into ψ.
  + intro x. destruct x.
    - term_simpl. reflexivity.
    - term_simpl. f_equal. apply H.
  + intro k. term_simpl. f_equal. apply H.
Qed.

Lemma tbind_pure {A : VSig} (φ : A {→} A) (M : term A) (EQ : φ ≡ ı) :
  bind φ M = M
 with vbind_pure {A : VSig} (φ : A {→} A) (V : value A) (EQ : φ ≡ ı) :
  bind φ V = V
 with jbind_pure {A : VSig} (φ : A {→} A) (J : jump A) (EQ : φ ≡ ı) :
  bind φ J = J.
Proof.
(* tbind_pure *)
{
  induction M as [ S V | S M₁ IHM₁ M₂ IHM₂ |].
  + term_simpl. f_equal. apply vbind_pure. apply EQ.
  + term_simpl. f_equal.
    - apply IHM₁. apply EQ.
    - apply IHM₂. apply EQ.
  + term_simpl. f_equal.
    apply jbind_pure. apply lift_id. apply EQ.
}
(* vbind_pure *)
{
  induction V as [ x | M ].
  + term_simpl. apply EQ.
  + term_simpl. f_equal. apply tbind_pure. apply lift_id. apply EQ.
}
(* jbind_pure *)
{
  pose proof EQ as [_ EQₖ].
  induction J as [q M].
  + term_simpl. destruct q as [k |].
    - specialize EQₖ with k.
      destruct (sub_k φ k) as [q E]. term_simpl in EQₖ. inversion EQₖ as [[Hq HE]].
      f_equal. term_simpl. apply tbind_pure. apply EQ.
    - f_equal. apply tbind_pure. apply EQ.
}
Qed.

Lemma eplug_fmap {A B : VSig} (φ : prod_arr A B) (E : ectx A) (M : term A) :
  fmap φ (eplug E M) = eplug (fmap φ E) (fmap φ M).
Proof.
  induction E; term_simpl; f_equal; assumption.
Qed.

Lemma eplug_bind {A B : VSig} (φ : A {→} B) (E : ectx A) M :
  eplug (bind φ E) (bind φ M) = bind φ (eplug E M).
Proof.
  induction E; term_simpl; f_equal; assumption.
Qed.

Lemma eplug_plug_comp {A : VSig} (E₂ E₁ : ectx A) (M : term A) :
  eplug E₂ (eplug E₁ M) = eplug (ecomp E₂ E₁) M.
Proof.
  induction E₂; term_simpl; f_equal; assumption.
Qed.

Lemma tbind_bind_comp {A B C : VSig} (φ₂ : B {→} C) (φ₁ : A {→} B) ψ (M : term A) (EQ : φ₂ ∘ φ₁ ≡ ψ) :
  bind φ₂ (bind φ₁ M) = bind ψ M
 with vbind_bind_comp {A B C : VSig} (φ₂ : B {→} C) (φ₁ : A {→} B) ψ (V : value A) (EQ : φ₂ ∘ φ₁ ≡ ψ) :
  bind φ₂ (bind φ₁ V) = bind ψ V
 with jbind_bind_comp {A B C : VSig} (φ₂ : B {→} C) (φ₁ : A {→} B) ψ (J : jump A) (EQ : φ₂ ∘ φ₁ ≡ ψ) :
  bind φ₂ (bind φ₁ J) = bind ψ J.
Proof.
(* tbind_bind_comp *)
{
  induction M as [ A V | A M₁ IHM₁ M₂ | A J].
  + term_simpl. f_equal. apply vbind_bind_comp. apply EQ.
  + term_simpl. f_equal.
    - apply IHM₁. apply EQ.
    - apply IHM₂. apply EQ.
  + term_simpl. f_equal.
    apply jbind_bind_comp. apply lift_comp. apply EQ.
}
(* vbind_bind_comp *)
{
  induction V as [ x | M ].
  + term_simpl. apply EQ.
  + term_simpl. f_equal. apply tbind_bind_comp. apply lift_comp. apply EQ.
}
(* jbind_bind_comp *)
{
  pose proof EQ as [_ EQₖ].

  induction J as [q M].
  term_simpl. destruct q as [k |].
  + specialize EQₖ with k. inversion EQₖ as [Hsub].
    destruct (sub_k φ₁ k) as [q E]. term_simpl.
    destruct q as [k' |].
    - destruct (sub_k φ₂ k') as [q' E'].
      destruct (sub_k ψ k) as [q'' E''].
      inversion Hsub. f_equal.
      rewrite <- eplug_bind.
      rewrite eplug_plug_comp. f_equal.
      apply tbind_bind_comp. apply EQ.
    - f_equal.
      rewrite <- eplug_bind. f_equal.
      apply tbind_bind_comp. apply EQ.
  + term_simpl. f_equal.
    apply tbind_bind_comp. apply EQ.
}
Qed.

Instance Bind_term  : Bind term  := { bind_pure := @tbind_pure; bind_bind_comp := @tbind_bind_comp }.
Instance Bind_value : Bind value := { bind_pure := @vbind_pure; bind_bind_comp := @vbind_bind_comp }.
Instance Bind_jump  : Bind jump  := { bind_pure := @jbind_pure; bind_bind_comp := @jbind_bind_comp }.

Lemma ebind_pure {A : VSig} (φ : A {→} A) (E : ectx A) (EQ : φ ≡ ı) :
  bind φ E = E.
Proof.
  induction E as [| E IHE M | V E ].
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    - apply IHE.
    - apply tbind_pure. apply EQ.
  + term_simpl. f_equal.
    - apply vbind_pure. apply EQ.
    - apply IHE.
Qed.

Lemma ebind_bind_comp {A B C : VSig} (φ₂ : B {→} C) (φ₁ : A {→} B) ψ (E : ectx A) (EQ : φ₂ ∘ φ₁ ≡ ψ) :
  bind φ₂ (bind φ₁ E) = bind ψ E.
Proof.
  induction E as [| E IHE M | V E ].
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    - apply IHE.
    - apply tbind_bind_comp. apply EQ.
  + term_simpl. f_equal.
    - apply vbind_bind_comp. apply EQ.
    - apply IHE.
Qed.

Instance Bind_ectx : Bind ectx := { bind_pure := @ebind_pure; bind_bind_comp := @ebind_bind_comp }.

Program Instance SubstShift_prod_arr_VSub_value_incV : SubstShift prod_arr VSub value incV.
Next Obligation.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. term_simpl. reflexivity.
Qed.

Program Instance SubstShift_prod_arr_VSub_ssub_incK : SubstShift prod_arr VSub ssub incK.
Next Obligation.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. term_simpl. reflexivity.
Qed.

Program Instance Subst_prod_arr_VSub : Subst prod_arr VSub.
Next Obligation.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. term_simpl. reflexivity.
Qed.
Next Obligation.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. term_simpl. reflexivity.
Qed.
Next Obligation.
  constructor;
  rename x into φ, y into ψ.
  + intro x. term_simpl. f_equal. apply H.
  + intro k. term_simpl. f_equal. f_equal. apply H.
Qed.

Definition VSub_id {A : VSig} :=
  {| sub_v := λ x : tv A, v_var x
   ; sub_k := λ k : kv A, s_sub (k_var k) e_hole |}.

Lemma VSub_id_id {A : VSig} :
  VSub_id ≡ arrow_id A.
Proof.
  constructor.
  + intro x. reflexivity.
  + intro k. reflexivity.
Qed.

Lemma VSub_comp {A B C : VSig} (f : B {→} C) g :
  f ∘ g
  ≡ {| sub_v := λ x : tv A, bind f (sub_v g x)
     ; sub_k := λ k : kv A,
        let (q', E2) := sub_k g k in
        match q' with
        | k_var k' =>
          let (q'', E1) := sub_k f k' in
          s_sub q'' (ecomp E1 (bind f E2))
        | k_tp => s_sub k_tp (bind f E2)
        end
    |}.
Proof.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. term_simpl.
    destruct (sub_k g k) as [q E].
    destruct q as [k' |].
    - destruct (sub_k f k') as [q' E']. term_simpl. reflexivity.
    - term_simpl. reflexivity.
Qed.

Lemma ecomp_bind {S T : VSig} (E1 : ectx S) (E2 : ectx S) (φ : S {→} T) :
  ecomp (bind φ E1) (bind φ E2) = bind φ (ecomp E1 E2).
Proof.
  induction E1.
  + term_simpl. reflexivity.
  + term_simpl. f_equal.
    apply IHE1.
  + term_simpl. f_equal.
    apply IHE1.
Qed.

Lemma tbind_eq {A B : VSig} (φ ψ : A {→} B) (M : term A) :
  φ ≡ ψ →
  bind φ M = bind ψ M
 with vbind_eq {A B : VSig} (φ ψ : A {→} B) (V : value A) :
  φ ≡ ψ →
  bind φ V = bind ψ V
 with jbind_eq {A B : VSig} (φ ψ : A {→} B) (J : jump A) :
  φ ≡ ψ →
  bind φ J = bind ψ J.
Proof.
(* tbind_eq *)
{
  intro EQ.
  induction M as [ A V | A M₁ IHM₁ M₂ | A J ].
  + term_simpl. f_equal. apply vbind_eq. apply EQ.
  + term_simpl. f_equal.
    - apply IHM₁. apply EQ.
    - apply IHM₂. apply EQ.
  + term_simpl. f_equal. apply jbind_eq. apply lift_proper. apply EQ.
}
(* vbind_eq *)
{
  intro EQ.
  induction V as [ x | M ].
  + term_simpl. apply EQ.
  + term_simpl. f_equal. apply tbind_eq. apply lift_proper. apply EQ.
}
(* jbind_eq *)
{
  intro EQ.
  pose proof EQ as [EQᵥ EQₖ].

  induction J as [q M].
  + term_simpl.
    destruct q as [k |].
    - rewrite (EQₖ k).
      destruct (sub_k ψ k) as [q E].
      f_equal. f_equal. apply tbind_eq. apply EQ.
    - f_equal. apply tbind_eq. apply EQ.
}
Qed.

Lemma ebind_eq {A B : VSig} (φ ψ : A {→} B) (E : ectx A) :
  φ ≡ ψ →
  bind φ E = bind ψ E.
Proof.
  intro EQ.
  induction E; term_simpl; f_equal;
  try assumption; apply tbind_eq || apply vbind_eq; try assumption.
Qed.

Program Instance Arrow_VSub : Arrow VSub.
Next Obligation.
  constructor.
  + intro x. term_simpl.
    rewrite bind_pure.
    - reflexivity.
    - apply VSub_id_id.
  + intro k. term_simpl.
    destruct (sub_k f k) as [q E]. term_simpl.
    destruct q; term_simpl; f_equal; apply bind_pure; apply VSub_id_id.
Qed. Next Obligation.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. term_simpl.
    destruct (sub_k f k) as [q E].
    rewrite ecomp_pure. reflexivity.
Qed. Next Obligation.
  constructor.
  + intro x. term_simpl.
    symmetry. apply bind_bind_comp.
    apply VSub_comp.
  + intro k. term_simpl.
    destruct (sub_k h k) as [q₁ E₁]; term_simpl.
    destruct q₁ as [k₁ |]; term_simpl.
    - destruct (sub_k g k₁) as [q₂ E₂]; term_simpl.
      destruct q₂ as [k₂ |]; term_simpl.
      * destruct (sub_k f k₂) as [q₃ E₃]; term_simpl.
        f_equal. rewrite <- ecomp_bind.
        rewrite ecomp_assoc.
        f_equal. symmetry. apply bind_bind_comp. apply VSub_comp.
      * f_equal. rewrite <- ecomp_bind.
        f_equal. symmetry. apply bind_bind_comp. apply VSub_comp.
    - f_equal. symmetry. apply bind_bind_comp. apply VSub_comp.
Qed. Next Obligation.
  constructor;
  pose proof H0 as [EQ₂ᵥ EQ₂ₖ];
  pose proof H as [EQ₁ᵥ EQ₁ₖ];
  rename x into φ₁, y into ψ₁, x0 into φ₂, y0 into ψ₂.
  + intro x. term_simpl.
    specialize EQ₂ᵥ with x. rewrite EQ₂ᵥ.
    replace (sub_v ψ₂ x) with (bind ψ₂ (v_var x)) by reflexivity.
    apply vbind_eq. apply H.
  + intro k. term_simpl.
    specialize EQ₂ₖ with k. rewrite EQ₂ₖ.
    destruct (sub_k ψ₂ k) as [q E]; term_simpl.
    destruct q as [k' |].
    - specialize EQ₁ₖ with k'. rewrite EQ₁ₖ.
      destruct (sub_k ψ₁ k') as [q' E'].
      f_equal. f_equal.
      apply ebind_eq. apply H.
    - f_equal. apply ebind_eq. apply H.
Qed.

Program Instance SubstBind_VSub_value_incV : SubstBind VSub value incV.
Next Obligation.
  constructor.
  + intro x. term_simpl.
    destruct x as [| x].
    - term_simpl. reflexivity.
    - term_simpl. reflexivity.
  + intro k. term_simpl.
    destruct (sub_k f k) as [q E]. term_simpl.
    destruct q as [k' |];
      term_simpl; f_equal; apply ecomp_pure.
Qed.

Program Instance SubstBind_VSub_ssub_incK : SubstBind VSub ssub incK.
Next Obligation.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. term_simpl.
    destruct k as [| k].
    - destruct v as [q E].
      destruct q as [k |].
      * term_simpl. destruct (sub_k f k) as [q' E'].
        rewrite ecomp_pure. reflexivity.
      * term_simpl. rewrite ecomp_pure. reflexivity.
    - term_simpl. destruct (sub_k f k) as [q E]. term_simpl.
      destruct q as [k' |].
      * term_simpl. rewrite ecomp_pure. reflexivity.
      * term_simpl. rewrite ecomp_pure. reflexivity.
Qed.

Lemma struct_subst_pure {A : VSig} (J : jump (incK A)) :
  struct_subst J e_hole = J.
Proof.
  unfold struct_subst.
  apply bind_pure.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. destruct k as [| k].
    - term_simpl. reflexivity.
    - term_simpl. reflexivity.
Qed.

Lemma fmap_struct_sub_comm {A B : VSig} (φ : prod_arr A B) E :
   (φ ↑) ̂ ∘ struct_sub (shift E) ≡ struct_sub (fmap (φ ↑) (shift E)) ∘ (φ ↑) ̂.
Proof.
  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. term_simpl.
    destruct k as [| k].
    - term_simpl.
      rewrite ecomp_pure.
      rewrite <- map_to_bind. f_equal.
      unfold shift.
      rewrite !map_map_comp'; reflexivity.
    - term_simpl. reflexivity.
Qed.

Lemma bind_struct_sub_comm {A B : VSig} (φ : A {→} B) (E : ectx A) :
  φ ↑ ∘ struct_sub (shift E) ≡ struct_sub (bind (φ ↑) (shift E)) ∘ φ ↑.
Proof.
  constructor.
  + intro x. term_simpl.

    destruct (sub_v φ x).
    - term_simpl. reflexivity.
    - term_simpl. f_equal.
      rewrite map_to_bind.
      rewrite bind_bind_comp'.
      rewrite lift_of_arrow.
      rewrite lift_comp by reflexivity.
      apply bind_proper; reflexivity.
  + intro k. destruct k as [| k].
    - term_simpl. rewrite ecomp_pure. reflexivity.
    - term_simpl. destruct (sub_k φ k) as [q E']. term_simpl.
      destruct q as [k' |].
      * term_simpl. rewrite ecomp_pure. f_equal.
        unfold shift.
        rewrite map_to_bind.
        rewrite bind_bind_comp'.
        apply bind_proper; reflexivity.
      * term_simpl. rewrite ecomp_pure. f_equal.
        unfold shift.
        rewrite map_to_bind.
        rewrite bind_bind_comp'.
        apply bind_proper; reflexivity.
Qed.

Lemma bind_struct_subst {A B : VSig} (φ : A {→} B) (J : jump (incK A)) (E : ectx A) :
  bind (φ ↑) (struct_subst J (shift E)) = struct_subst (bind (φ ↑) J) (bind (φ ↑) (shift E)).
Proof.
  unfold struct_subst.
  rewrite !bind_bind_comp'.
  apply bind_proper; [| reflexivity].
  apply bind_struct_sub_comm.
Qed.

Lemma fmap_struct_subst {A B : VSig} (φ : prod_arr A B) (J : jump (incK A)) (E : ectx A) :
  fmap (φ ↑) (struct_subst J (shift E)) = struct_subst (fmap (φ ↑) J) (fmap (φ ↑) (shift E)).
Proof.
  unfold struct_subst. symmetry.
  erewrite bind_map_comm.
  + reflexivity.
  + symmetry. apply fmap_struct_sub_comm.
Qed.

Lemma struct_subst_comp {A : VSig} (E₂ E₁ : ectx A) (J : jump (incK A)) :
  struct_subst (struct_subst J (shift E₁)) (shift E₂) = struct_subst J (shift (ecomp E₂ E₁)).
Proof.
  unfold struct_subst.
  rewrite !bind_bind_comp'.
  apply bind_proper; [| reflexivity ].

  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. destruct k as [| k].
    - term_simpl. f_equal.
      rewrite <- ecomp_kshift. f_equal.
      unfold shift.
      rewrite !map_to_bind with (f := mk_shift).
      rewrite bind_bind_comp'.
      apply bind_proper; reflexivity.
    - term_simpl. f_equal.
Qed.

Lemma subst_struct_subst {A : VSig} (E₂ E₁ : ectx A) q J :
  subst (struct_subst J (shift E₁)) (s_sub q E₂) = subst J (s_sub q (ecomp E₂ E₁)).
Proof.
  unfold subst, struct_subst.
  rewrite !bind_bind_comp'.
  apply bind_proper; [| reflexivity ].

  constructor.
  + intro x. term_simpl. reflexivity.
  + intro k. destruct k as [| k].
    - term_simpl. f_equal.
    - term_simpl. f_equal.
Qed.
