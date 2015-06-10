Require Import Category.RComod.
Require Import Category.Stream.Category.
Require Import Category.Stream.Model.
Require Import Category.TriMat.Axioms.
Require Import Category.TriMat.Model.
Require Import Theory.Category.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.

Module Diag (Import TE : Typ).

  Module Import Tri := TriMat.Model.Terminality TE.
  Module Str := Stream.Model.Terminality.

  Definition 𝒅𝒊𝒂𝒈 := Str.τ Stream.make ⦃ T ≔ 𝑻𝒓𝒊 ; tail ≔ Comodule.Morphism.compose 𝑪𝒖𝒕 𝑹𝒆𝒔𝒕 ⦄.

End Diag.
