(*

   Benedikt Ahrens and Régis Spadotti

   Coinitial semantics for redecoration of triangular matrices

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of functor from rel. comonads to rel. comonads with cut

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

(** * Canonical cut **)

(*------------------------------------------------------------------------------
  -- ＣＡＮＯＮＩＣＡＬ  ＣＵＴ
  ----------------------------------------------------------------------------*)
(** ** Definition **)

Section Defs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞 𝒟) (E : 𝒞) `{!CartesianStrongMonoidal F}.

  Program Definition 𝑪𝒖𝒕 : Functor (𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 F) (𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝒕 F E) :=
    Functor.make  ⦃ F    ≔ λ T ∙ RelativeComonadWithCut.make  ⦃ RelativeComonad  ≔ T
                                                              ; cut              ≔ λ A ∙ Lift(T) ⋅ π₂ ⦄
                  ; map  ≔ λ T S ∙ λ τ ↦ RelativeComonadWithCut.make ⦃ RelativeComonad-τ ≔ τ ⦄ ⦄.
  (** cut-counit **)
  Next Obligation.
    now rewrite counit_cobind.
  Qed.
  (** cobind-cobind **)
  Next Obligation.
    do 2 rewrite cobind_cobind. apply Π.cong.
    now rewrite compose_assoc, counit_cobind,
                <- compose_assoc, Fπ₂_φ_inv, π₂_compose.
  Qed.
  (** cut-cobind **)
  Next Obligation.
    now rewrite (RelativeComonad.τ_counit τ), <- compose_assoc, RelativeComonad.τ_commutes.
  Qed.
  (** map-cong **)
  Next Obligation.
    intros f g eq_fg x. auto.
  Qed.
  (** map-id **)
  Next Obligation.
    reflexivity.
  Qed.
  (** map-compose **)
  Next Obligation.
    reflexivity.
  Qed.

  Program Definition 𝑼 : Functor (𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝒕 F E) (𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 F) :=
    Functor.make ⦃ F ≔ λ T ∙ T ; map ≔ λ A B ∙ λ τ ↦ τ ⦄.
  (** map-cong **)
  Next Obligation.
    repeat intro; auto.
  Qed.
  (** map-id **)
  Next Obligation.
    reflexivity.
  Qed.
  (** map-compose **)
  Next Obligation.
    reflexivity.
  Qed.

End Defs.
