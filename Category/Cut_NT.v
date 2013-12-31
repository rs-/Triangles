Require Import Category.RComonad.
Require Import Category.RComonadWithCut.
Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.NaturalTransformation.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.CartesianStrongMonoidal.
Require Import Theory.PrecompositionWithProduct.
Require Import Theory.PushforwardComodule.

Generalizable All Variables.

Section CUT_NT.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} {F : Functor 𝒞 𝒟} `{!CartesianStrongMonoidal F}
          {E : 𝒞} (T : RelativeComonadWithCut F E).


  (** Functor 𝑻 : 𝒞 → 𝒟 **)
  Notation 𝑻 := (Lift(T)).

  Notation "'𝑻(𝑬×─)'" := (MLift ([T][E×─])).

  Program Definition 𝑪𝒖𝒕 : NaturalTransformation 𝑻(𝑬×─) 𝑻 :=
    NaturalTransformation.make (λ A ∙ T⋅cut).
  Next Obligation.
    now rewrite cut_cobind.
  Qed.

End CUT_NT.



