(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of the category of comodules over a fixed comonad towards a fixed category

*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Theory.CoProduct.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＣＯＭＯＤＵＬＥＳ
  ----------------------------------------------------------------------------*)
(** * Category of Comodules **)

(** ** Category definition **)

Section Definitions.

  Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category).

  Implicit Types (A B C D : Comodule T ℰ).

  Import Comodule.Morphism.

  Infix "⇒" := Hom.
  Infix "∘" := compose.

  Lemma left_id A B  (f : A ⇒ B) : id ∘ f ≈ f.
  Proof.
    intro x; simpl. rewrite left_id. reflexivity.
  Qed.

  Lemma right_id A B (f : A ⇒ B) : f ∘ id ≈ f.
  Proof.
    intro x; simpl. now rewrite right_id.
  Qed.

  Lemma compose_assoc A B C D (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D) : h ∘ g ∘ f ≈ h ∘ (g ∘ f).
  Proof.
    intro x; simpl. now rewrite compose_assoc.
  Qed.

  Canonical Structure 𝑹𝑪𝒐𝒎𝒐𝒅 : Category :=
    mkCategory left_id right_id compose_assoc.

End Definitions.

(** * Some constructions on comodules **)
Section Precomposition.

  Context {𝒞 𝒟 ℰ 𝒳 : Category} (F : Functor 𝒞 𝒟) (G : Functor ℰ 𝒳) (T : RelativeComonad F).

  Program Definition functor_precomposition : Functor (𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ) (𝑹𝑪𝒐𝒎𝒐𝒅 T 𝒳) :=
    Functor.make  ⦃ F    ≔ λ M ∙ Comodule.make  ⦃ M        ≔ λ X ∙ G (M X)
                                                ; mcobind  ≔ λ _ _ ∙ λ f ↦ G⋅(mcobind M f) ⦄
                  ; map  ≔ λ _ _ ∙ λ α ↦ Comodule.make ⦃ α ≔ λ C ∙ G⋅(α C) ⦄
                  ⦄.
  Next Obligation. solve_proper. Qed.
  Next Obligation. rewrite mcobind_counit. now rewrite <- identity. Qed.
  Next Obligation. rewrite <- map_compose. now rewrite mcobind_mcobind. Qed.
  Next Obligation. rewrite <- map_compose. rewrite α_commutes. now rewrite <- map_compose. Qed.
  Next Obligation. intros f f' eq_ff' x. simpl. rewrite (eq_ff' x). reflexivity. Qed.
  Next Obligation. now rewrite identity. Qed.
  Next Obligation. now rewrite <- map_compose. Qed.

End Precomposition.

Section Coproduct.

  Context {𝒞 𝒟 ℰ: Category} `{CP : BinaryCoproduct ℰ} (F : Functor 𝒞 𝒟) (T : RelativeComonad F).

  Program Definition mcoprod : 𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ → 𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ → 𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ :=
    λ M N ∙ Comodule.make  ⦃ M        ≔ λ X ∙ M(X) ⊎ N(X)
                           ; mcobind  ≔ λ _ _ ∙ λ f ↦ mcobind M f -⊎- mcobind N f ⦄.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    rewrite <- coproduct_postcompose, coproduct_eta, Category.left_id.
    repeat rewrite mcobind_counit.
    now rewrite coproduct_arrow_id.
  Qed.
  Next Obligation.
    do 2 rewrite <- mcobind_mcobind.
    etransitivity. eapply coproduct_postcompose.
    now do 2 rewrite <- Category.compose_assoc.
  Qed.

  Program Definition mCmor {M N P : 𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ} : [ M ⇒ P ⟶ N ⇒ P ⟶ mcoprod M N ⇒ P ] :=
    λ f g ↦₂ Comodule.make ⦃ α ≔ λ X ∙ [ f X , g X ] ⦄.
  Next Obligation. setoid_rewrite coproduct_precompose at 2.
                   etransitivity. eapply coproduct_postcompose.
  repeat rewrite α_commutes. reflexivity.
  Qed.
  Next Obligation.
    intros ? ? eq1 ? ? eq2 x; simpl. now rewrite (eq1 x), (eq2 x).
  Qed.

  Program Definition mι₁ {M N : 𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ} : M ⇒ mcoprod M N :=
    Comodule.make ⦃ α ≔ λ X ∙ ι₁[ M X , N X ] ⦄.
  Next Obligation. now rewrite ι₁_compose. Qed.
  Program Definition mι₂ {M N : 𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ} : N ⇒ mcoprod M N :=
    Comodule.make ⦃ α ≔ λ X ∙ ι₂[ M X , N X ] ⦄.
  Next Obligation. now rewrite ι₂_compose. Qed.


  Program Definition BinaryCoproduct_Comodule : BinaryCoproduct (𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ) :=
    BinaryCoproduct.make ⦃ Category ≔ 𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ
                         ; _+_ ≔ mcoprod
                         ; [_,_] ≔ @mCmor _ _
                         ; ι₁ ≔ mι₁
                         ; ι₂ ≔ mι₂ ⦄.
  Next Obligation.
    now rewrite ι₁_compose.
  Qed.
  Next Obligation.
    now rewrite ι₂_compose.
  Qed.
  Next Obligation.
    now apply Cpmor_universal.
  Qed.

End Coproduct.



