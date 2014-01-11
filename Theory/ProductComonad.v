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
  -- ＰＲＯＤＵＣＴ  ＩＮ  ＣＯＮＴＥＸＴ 
  ----------------------------------------------------------------------------*)

Section ProductInContext.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} {F : Functor 𝒞  𝒟}
          {E : 𝒞} `{!CartesianStrongMonoidal F} {T : RelativeComonad F}.

  Program Definition product_in_context_comonad : RelativeComonad F :=
    RelativeComonad.make 
           (λ C ∙ T (E × C)) 
           (λ C ∙ F ⋅ π₂  ∘ T⋅counit)
           ( λ A B ∙ λ f ↦ T⋅cobind (φ⁻¹ ∘ ⟨ F ⋅ π₁ ∘ T⋅counit , f  ⟩))
           .
  Next Obligation.
    intros f g eq_fg. now rewrite eq_fg.
  Qed.
  Next Obligation.
    rewrite <- ∘-×. rewrite <- compose_assoc. rewrite iso_right.
    rewrite left_id. rewrite cobind_counit. reflexivity.
  Qed.
  Next Obligation.
    repeat rewrite compose_assoc.
    rewrite counit_cobind.
    repeat rewrite <- compose_assoc.
    rewrite Fπ₂_φ_inv. 
    repeat rewrite <- compose_assoc. 
    rewrite π₂_compose. reflexivity.
  Qed.
  Next Obligation.
    rewrite cobind_compose.
    repeat rewrite compose_assoc.
    rewrite ∘-×.
    repeat rewrite compose_assoc.
    rewrite counit_cobind.
    rewrite <- compose_assoc.
    rewrite Fπ₁_φ_inv.
    rewrite π₁_compose.
    reflexivity.
  Qed.

End ProductInContext.


 