(*

   Benedikt Ahrens and Régis Spadotti

   Coinitial semantics for redecoration of triangular matrices

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  - definition of comodule obtained by precomposing with product
  - corresponding action on morphisms of comodules

*)

Require Import Category.RComod.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.Isomorphism.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.CartesianStrongMonoidal.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＰＲＥＣＯＭＰＯＳＩＴＩＯＮ  ＷＩＴＨ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** * Precomposition with product **)

(** ** Definitions **)

Section PrecompositionWithProduct.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} {F : Functor 𝒞  𝒟}
          {E : 𝒞} `{!CartesianStrongMonoidal F} {T : RelativeComonadWithCut F E}
          {ℰ : Category} (M : Comodule T ℰ).

  Program Definition precomposition_with_product : Comodule T ℰ :=
    Comodule.make  ⦃ M        ≔ λ C ∙ M (E × C)
                   ; mcobind  ≔ λ A B ∙ λ f ↦ M⋅mcobind (T⋅extend(f)) ⦄.
  Next Obligation.
    intros f g eq_fg. now rewrite eq_fg.
  Qed.
  Next Obligation.
    rewrite cut_counit. rewrite <- ∘-×. rewrite <- compose_assoc. rewrite iso_right.
    rewrite left_id. rewrite mcobind_counit. reflexivity.
  Qed.
  Next Obligation.
    rewrite mcobind_mcobind. apply Π.cong. repeat rewrite compose_assoc.
    rewrite ∘-×. rewrite cut_cobind. unfold Extend. simpl.
    repeat rewrite compose_assoc. rewrite counit_cobind.
    repeat rewrite <- compose_assoc. rewrite Fπ₁_φ_inv. rewrite π₁_compose. reflexivity.
  Qed.

End PrecompositionWithProduct.

Arguments precomposition_with_product {_ _ _ _ _} _ {_ _ _} _.

Notation "M [ E '×─' ] " := (precomposition_with_product E M) (at level 0).

(** ** Precomposition with product on morphisms **)
Section Morphisms.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞  𝒟)
          (E : 𝒞) `{!CartesianStrongMonoidal F} (T : RelativeComonadWithCut F E)
          (ℰ : Category) (M : Comodule T ℰ) (N : Comodule T ℰ) (α : M ⇒ N).

  Program Definition precomposition_with_product_mor : ‵ M[E×─] ⇒ N[E×─] ′ :=
    Comodule.make ⦃ α ≔ λ A ∙ α (E × A) ⦄.
  Next Obligation.
    now rewrite α_commutes.
  Qed.

End Morphisms.

Arguments precomposition_with_product_mor {_ _ _ _ _} _ {_ _ _ _ _} _.

Notation "α ［ E '×─' ］" := (precomposition_with_product_mor E α) (at level 0).
