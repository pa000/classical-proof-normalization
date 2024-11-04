Require Import Utf8.
Require Import Binding.Lib Binding.Product Binding.Env Binding.Set.
Require Import Syntax Typing Semantics.
Require Import String.
Require Import Relation_Operators.

Local Open Scope bind_scope.

Notation "A → B" := (tp_arrow A B).
Notation "¬ A" := (tp_arrow A tp_bottom).

(* -------------------------------- *)

(* λy.C(λ_.tp y) : ⊥ → A *)
Example abort : term ⟨∅, ∅⟩ :=
  v_lam (t_ctrl (j_jmp k_tp (v_var VZ))).

Example abort_type : T[ empty_env ⊢ abort ∷ tp_bottom → (tp_atom "A") ].
Proof.
  apply T_Abs.
  apply T_Ctrl.
  apply J_Tp.
  apply T_Var.
  simpl. reflexivity.
Qed.

Example abort_red : ¬ ∃ M, abort →ₜ M.
Proof.
  intro. destruct H; repeat
    match goal with
    | [ H: tred _ _ |- _ ] => inversion H; subst; clear H
    | [ H: jred _ _ |- _ ] => inversion H; subst; clear H
    | [ H: vred _ _ |- _ ] => inversion H; subst; clear H
    end.
Qed.

(* -------------------------------- *)

(* λy.C(λk. tp (y (λx.throw k x))) : ¬¬A → A *)
(* where throw k f = C(λ_. k f) *)
Example dn : term ⟨∅, ∅⟩ := 
  v_lam
    (t_ctrl (j_jmp
      k_tp
      (t_app
        (v_var VZ)
        (v_lam
          (t_ctrl (j_jmp
            (k_var (VS VZ))
            (v_var VZ)
          ))
        )
      )
    )).

Example dn_type : T[ empty_env ⊢ dn ∷ ¬¬(tp_atom "A") → tp_atom "A" ].
Proof.
  apply T_Abs.
  apply T_Ctrl.
  apply J_Tp.
  eapply T_App.
  + apply T_Var. simpl. reflexivity.
  + apply T_Abs.
    apply T_Ctrl.
    eapply J_Cont.
    - constructor. simpl. reflexivity.
    - apply T_Var.
      simpl. reflexivity.
Qed.

Example dn_red : ¬ ∃ M, dn →ₜ M.
Proof.
  intro. destruct H; repeat
    match goal with
    | [ H: tred _ _ |- _ ] => inversion H; subst; clear H
    | [ H: jred _ _ |- _ ] => inversion H; subst; clear H
    | [ H: vred _ _ |- _ ] => inversion H; subst; clear H
    end.
Qed.

(* -------------------------------- *)

(* λy. C(λk.k (y (λx.throw k x))) : ((A → B) → A) → A *)
Example peirce : term ⟨∅, ∅⟩ :=
  v_lam
    (t_ctrl (j_jmp
      (k_var VZ)
      (t_app
        (v_var VZ)
        (v_lam
          (t_ctrl (j_jmp
            (k_var (VS VZ))
            (v_var VZ)
          ))
        )
      )
    )).

Example peirce_type : T[ empty_env ⊢ peirce ∷ ((tp_atom "A" → tp_atom "B") → tp_atom "A") → (tp_atom "A") ].
Proof.
  apply T_Abs.
  apply T_Ctrl.
  eapply J_Cont.
  + constructor. simpl. reflexivity.
  + eapply T_App.
    - apply T_Var.
      simpl. reflexivity.
    - apply T_Abs.
      apply T_Ctrl.
      eapply J_Cont.
      * constructor. simpl. reflexivity.
      * apply T_Var.
        simpl. reflexivity.
Qed.

Example peirce_red : ¬ ∃ M, peirce →ₜ M.
Proof.
  intro. destruct H as [M Htred_peirce].
  inversion Htred_peirce as [| | | | ? V Hvred_peirce | | |]; subst.
  inversion Hvred_peirce as [ ? M Htred_ctrl ]; subst.
  inversion Htred_ctrl as [| | | ? HshiftM | | | | a1 J Hjred_jmp a4 ]; subst.
  + (* tred_C_elim *)
    destruct M; inversion HshiftM as [[ HshiftM1 HshiftM2 ]]; clear HshiftM1.
    destruct M2 as [ V | |]; inversion HshiftM2 as [ HshiftV ].
    destruct V as [| M3 ]; inversion HshiftV as [ HshiftM3 ].
    destruct M3 as [| | J ]; inversion HshiftM3 as [ HshiftJ ].
    destruct J as [ q M4 ]; inversion HshiftJ as [ [ Hshiftq HshiftM4 ] ]; clear HshiftM4.
    destruct q; inversion Hshiftq as [ Hshiftk ].
    destruct k; inversion Hshiftk.
  + (* tred_ctrl *)
    destruct J as [ q M ]; inversion Hjred_jmp as [| ? ? ? Htred_tapp ]; subst.
    destruct M; inversion Htred_tapp as [| | | | | M M1' M2' Htred_var | M M1' M2' Htred_lam |];
    [ subst M1' M M2'; clear H2 | subst M1' M M2' M1 ].
    - (* tred_app_L *)
      destruct M1 as [ V | |]; inversion Htred_var as [| | | | ? ? Hvred_var | | | ]; subst.
      destruct V; inversion Hvred_var.
    - (* tred_app_R *)
      destruct M2 as [ V | |]; inversion Htred_lam as [| | | | ? ? Hvred_lam | | | ]; subst.
      destruct V as [ | M ]; inversion Hvred_lam as [ ? ? Htred_ctrl2 ]; subst.
      destruct M as [| | J ]; inversion Htred_ctrl2 as [ | | | | | | | ? ? Hjred_jmp2 ]; subst.
      destruct J as [ ? M ]; inversion Hjred_jmp2 as [| ? ? ? Htred_var ]; subst.
      destruct M as [ V | |]; inversion Htred_var as [| | | | ? ? Hvred_var | | |]; subst.
      destruct V; inversion Hvred_var.
Qed.

(* ------------------------------------------ *)
(* Example reduction taken from Remark 6. [1] *)

Inductive const : Set :=
  | const_one : const.

Notation "1" := (v_var const_one).
Definition I {S : VSig} : term S := (v_lam (v_var VZ)).

(* (C(λk. tp ((λq.q I) (λf. throw k f)))) 1 *)
Example id_one : term ⟨const, ∅⟩ :=
  t_app
    (t_ctrl (j_jmp
      k_tp
      (t_app
        (v_lam
          (t_app (v_var VZ) I)
        )
        (v_lam
          (t_ctrl (j_jmp
            (k_var (VS VZ))
            (v_var VZ)
          ))
        )
      )
    ))
    1.

Example id_one_red :
  id_one →+ₜ 1.
Proof.
  unfold id_one.
  (* (C(λk. tp ((λq.q I) (λf. throw k f)))) 1 *)
  (*            ^^^^^^^^^^^^^^^^^^^^^^^^ (beta) *)
  eapply t1n_trans.
  { apply tred_app_L.
    apply tred_ctrl.
    apply jred_jmp.
    apply tred_beta. }
  term_simpl.
  (* (C(λk. tp ((λf. throw k f) I))) 1 *)
  (*            ^^^^^^^^^^^^^^^^^ (beta) *)
  eapply t1n_trans.
  { apply tred_app_L.
    apply tred_ctrl.
    apply jred_jmp.
    apply tred_beta. }
  term_simpl.
  (* (C(λk. tp (throw k I))) 1 *)
  (* ^^^^^^^^^^^^^^^^^^^^^^^^^ (C_L) *)
  eapply t1n_trans.
  { apply tred_C_L. }
  unfold struct_subst; term_simpl.
  (* C(λk. tp (throw k (I 1))) *)
  (*       ^^^^^^^^^ (C_idem) *)
  eapply t1n_trans.
  { apply tred_ctrl.
    apply jred_C_idem. }
  term_simpl.
  (* C(λk. k (I 1)) *)
  (*          ^^^ (beta) *)
  eapply t1n_trans.
  { apply tred_ctrl.
    apply jred_jmp.
    apply tred_beta. }
  term_simpl.
  (* C(λk. k 1) *)
  (* ^^^^^^^ (C_elim) *)
  apply t1n_step.
  apply tred_C_elim with (M := 1 : value ⟨_, _⟩).
Qed.
