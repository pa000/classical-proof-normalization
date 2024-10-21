Require Import Utf8.
Require Import Syntax.
From TLC Require Import LibLN.

Reserved Notation "M '-->' N" (at level 90).

Inductive red : trm → trm → Prop :=
  | red_beta : ∀ M V,
    body M →
    value V →
    trm_app (trm_abs M) V --> M ^^ V
  | red_C_elim : ∀ M,
    term M →
    trm_ctr (trm_app (trm_bvar 0) M) --> M
  | red_C_L : ∀ J N,
    jump J →
    trm_app (trm_ctr J) N --> trm_ctr (jump_subst J (λ P, trm_app P N))
  | red_C_R : ∀ V J,
    value V →
    jump J →
    trm_app V (trm_ctr J) --> trm_ctr (jump_subst J (λ P, trm_app V P))
  | red_idem : ∀ k' J,
    value k' →
    jump J →
    trm_ctr (trm_app k' (trm_ctr J)) --> trm_ctr (J ^^ k')

  | red_app_L : ∀ M M' N,
    M --> M' →
    term N →
    trm_app M N --> trm_app M' N
  | red_app_R : ∀ M N N',
    term M →
    N --> N' →
    trm_app M N --> trm_app M N'
  | red_abs : ∀ L M M',
    (∀ x, x \notin L →
      M ^^ x --> M' ^^ x) →
    trm_abs M --> trm_abs M'
  | red_ctr : ∀ L M M',
    (∀ x, x \notin L →
      M ^^ x --> M' ^^ x) →
    trm_ctr M --> trm_ctr M'

where "M --> N" := (red M N).
