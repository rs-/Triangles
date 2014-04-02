Require Import InfiniteTriangles.redecInfiniteTriangles8_4.
Require Import Category.Setoids.
Require Import Category.Sets.
Require Import Category.Sets_Setoids.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Category.RComonadWithCut.
Require Import Category.ITrees.
Require Import Category.StreamFinal.
Require Import Category.Coinitiality.
Require Import Category.Stream.
Require Import Category.TriMat.
Require Import Theory.Category.
Require Import Theory.InitialTerminal.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.PrecompositionWithProduct.
Require Import Theory.PushforwardComodule.


Module Singleton <: Elt.

  Definition E := unit.

End Singleton.

Module Diag (Import TE : Elt).

  Module Import Tri := Tri_Terminal TE.
  Module Import ITree := ITree_Terminal Singleton.

  Definition 𝒅𝒊𝒂𝒈 := ITree.τ Stream.make ⦃ T ≔ 𝑻𝒓𝒊 ; tail ≔ λ _ ∙ 𝑪𝒖𝒕 ∘ 𝑹𝒆𝒔𝒕 ⦄.

End Diag.