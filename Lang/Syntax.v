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
Inductive katom (A : Set) : Set :=
  | k_var   : A → katom A
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
  | j_jmp   : katom (kv A) → term A → jump A.

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

(* We use structural substitution with jumps.
   J[q E/k] means replace every occurence of k N with q E[N] in J. *)
Inductive ssub (A : VSig) : Type :=
  | s_sub : katom (kv A) → ectx A → ssub A.

Arguments s_sub & {A}.

(* ========================================================================= *)
(* Mapping, i.e. variable renaming *)

Definition kmap {A B : Set} (f : A [→] B) (q : katom A) : katom B :=
  match q with
  | k_var k => k_var (f k)
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
  | j_jmp q t => j_jmp (kmap (arr₂ φ) q) (tmap φ t)
  end.

Instance FMap_term  : FunctorCore term  := @tmap.
Instance FMap_value : FunctorCore value := @vmap.
Instance FMap_jump  : FunctorCore jump  := @jmap.

Fixpoint emap {A B : VSig} (φ : prod_arr A B) (E : ectx A) : ectx B :=
  match E with
  | e_hole     => e_hole
  | e_appl E t => e_appl (emap φ E) (tmap φ t)
  | e_appr v E => e_appr (vmap φ v) (emap φ E)
  end.

Instance FMap_ectx : FunctorCore ectx := @emap.

Definition smap {A B : VSig} (φ : prod_arr A B) (s : ssub A) : ssub B :=
  match s with
  | s_sub q E => s_sub (kmap (arr₂ φ) q) (emap φ E)
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

Definition struct_subst {A : VSig} (j : jump (incK A)) (E : ectx (incK A)) : jump (incK A) :=
  bind {|
    sub_v := λ v, v_var v : value (incK A)
  ; sub_k := λ k,
      match k with
      | VZ   => s_sub (k_var VZ) E
      | VS y => s_sub (k_var (VS y)) e_hole
      end
  |} j.

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
