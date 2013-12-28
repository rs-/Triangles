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
          (F : Functor 𝒞 𝒟) (E : 𝒞) `{!CartesianStrongMonoidal F}.


  Section Obj.

   Context (T : RelativeComonad F).

  Program Definition CanonicalCut : RelativeComonadWithCut F E :=  
    RelativeComonadWithCut.mkRelativeComonadWithCut (E:=E) (T:=T)(cut:=fun A => lift T (π₂[E, A])) _ _ .
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
    rewrite Fπ₂_φ_inv.
    rewrite π₂_compose.
    reflexivity.
  Qed.

  End Obj.

  Section Mor.
 
    Context {T S : RelativeComonad F} {tau : RelativeComonad.Morphism T S}.
    
    Program Definition CanonicalCutMor : RelativeComonadWithCut.Morphism
                                        (CanonicalCut T) (CanonicalCut S) :=
         RelativeComonadWithCut.mkMorphism (τ:=tau) _ .
    Next Obligation.
      rewrite <- τ_commutes.
      rewrite compose_assoc.
      rewrite <- τ_counit.
      reflexivity.
    Qed.
  
  End Mor.

End Defs.


    

