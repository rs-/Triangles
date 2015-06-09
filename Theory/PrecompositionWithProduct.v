(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  - definition of comodule obtained by precomposing with product
  - corresponding action on morphisms of comodules

*)

(* Require Import Category.RComod. *)
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.Isomorphism.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.ProductPreservingFunctor.

Generalizable All Variables.

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＰＲＥＣＯＭＰＯＳＩＴＩＯＮ  ＷＩＴＨ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** * Precomposition with product **)

(** ** Definitions **)

Section PrecompositionWithProduct.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} {F : Functor 𝒞  𝒟}
          {E : 𝒞} `{!ProductPreservingFunctor F} {T : RelativeComonadWithCut F E}
          {ℰ : Category} (M : Comodule T ℰ).

  Program Definition precomposition_with_product : Comodule T ℰ :=
    Comodule.make  ⦃ M        ≔ λ C ∙ M (E × C)
                   ; mcobind  ≔ λ A B ∙ λ f ↦ M⋅mcobind (T⋅extend(f)) ⦄.
  Next Obligation.
    cong. cong_r. cong_r. now cong_l.
  Qed.
  Next Obligation.
    etrans. cong. cong_r. cong_r. apply cut_counit.
    etrans. cong. cong_r. sym. apply ∘-×.
    etrans. cong. rew compose_assoc.
    etrans. cong. cong_l. apply iso_right.
    etrans. cong. rew left_id. apply mcobind_counit.
  Qed.
  Next Obligation.
    etrans. apply mcobind_mcobind.
    cong.
    etrans. apply compose_assoc.
    etrans. cong_r. apply ∘-×.
    sym. etrans. cong_r. cong_r. etrans. apply compose_assoc.
    cong_r. apply cut_cobind. sym.
    unfold Extend. simpl.
    etrans. cong_r. cong_l. etrans. apply compose_assoc. cong_r.
    apply counit_cobind. etrans. cong_r. cong_l. rew compose_assoc.
    etrans. cong_r. cong_l. cong_l. apply Fπ₁_φ_inv.
    etrans. cong_r. cong_l. apply π₁_compose.
    sym; etrans. cong_r. cong_r. rew compose_assoc. refl.
  Qed.

End PrecompositionWithProduct.

Arguments precomposition_with_product {_ _ _ _ _} _ {_ _ _} _.

Notation "M [ E '×─' ] " := (precomposition_with_product E M) (at level 0).

(** ** Precomposition with product on morphisms **)
Section Morphisms.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞  𝒟)
          (E : 𝒞) `{!ProductPreservingFunctor F} (T : RelativeComonadWithCut F E)
          (ℰ : Category) (M : Comodule T ℰ) (N : Comodule T ℰ) (α : Comodule.Morphism.Hom M N).

  Program Definition precomposition_with_product_mor : ‵ Comodule.Morphism.Hom M[E×─] N[E×─] ′ :=
    Comodule.make ⦃ α ≔ λ A ∙ α (E × A) ⦄.
  Next Obligation.
    apply α_commutes.
  Qed.

End Morphisms.

Arguments precomposition_with_product_mor {_ _ _ _ _} _ {_ _ _ _ _} _.

Notation "α ［ E '×─' ］" := (precomposition_with_product_mor E α) (at level 0).
