Require Import Category.RComonad.
Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.CartesianStrongMonoidal.
Require Import Theory.RelativeComonadWithCut.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ  ＷＩＴＨ  ＣＵＴ
  ----------------------------------------------------------------------------*)

Section Defs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          (F : Functor 𝒞 𝒟) (E : 𝒞) `{!CartesianStrongMonoidal F}
           {T : RelativeComonad F}.

  Program Definition CanonicalCut :=  
    RelativeComonadWithCut.make T (fun A => lift T (π₂[E, A])).
  Next Obligation.
    rewrite counit_cobind.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite cobind_compose.
    rewrite cobind_compose.
    repeat rewrite compose_assoc.
    rewrite counit_cobind.
    repeat rewrite <- compose_assoc.
    

