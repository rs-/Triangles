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

  Program Definition product_in_context : RelativeComonad F :=
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
    apply Π.cong. repeat rewrite compose_assoc.
    rewrite ∘-×. rewrite cut_cobind. unfold Extend. simpl.
    repeat rewrite compose_assoc. rewrite counit_cobind.
    assert (eq_π₁ : ∀ A B : 𝒞, F ⋅ π₁[A , B] ∘ φ⁻¹ ≈ π₁).
    {
      intros A B. assert (eq_F : F ⋅ π₁[A , B] ≈ π₁ ∘ φ). unfold φ. now rewrite π₁_compose.
      rewrite eq_F. rewrite compose_assoc. rewrite iso_left. now rewrite right_id.
    }
    repeat rewrite <- compose_assoc. rewrite eq_π₁. rewrite π₁_compose. reflexivity.
  Qed.


 