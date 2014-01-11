(**

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

Require Import Category.RComonad.
Require Import Category.RComonadWithCut.
Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Product.
Require Import Theory.CartesianStrongMonoidal.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＮＯＮＩＣＡＬ  ＣＵＴ
  ----------------------------------------------------------------------------*)

Section Defs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞 𝒟) (E : 𝒞) `{!CartesianStrongMonoidal F}.

  Program Definition 𝑪𝒖𝒕 : Functor (𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 F) (𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝒕 F E) :=
    Functor.make
      (λ T ∙ RelativeComonadWithCut.make T (λ A ∙ Lift(T) ⋅ π₂))
      (λ T S ∙ λ τ ↦ RelativeComonadWithCut.Morphism.make τ).
  Next Obligation.
    now rewrite counit_cobind.
  Qed.
  Next Obligation.
    do 2 rewrite cobind_cobind. apply Π.cong.
    now rewrite compose_assoc, counit_cobind,
                <- compose_assoc, Fπ₂_φ_inv, π₂_compose.
  Qed.
  Next Obligation.
    now rewrite (RelativeComonad.τ_counit τ), <- compose_assoc, RelativeComonad.τ_commutes.
  Qed.
  Next Obligation.
    intros f g eq_fg x. auto.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.

  Program Definition 𝑼 : Functor (𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝒕 F E) (𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 F) :=
    Functor.make (λ T ∙ T) (λ A B ∙ λ τ ↦ τ).
  Next Obligation.
    repeat intro; auto.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.

End Defs.