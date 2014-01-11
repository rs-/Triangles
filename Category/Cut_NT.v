(**

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

(** 

  Content of this file:
  
  a cut operation is a natural transformation

*)

Require Import Category.RComonad.
Require Import Category.RComonadWithCut.
Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.NaturalTransformation.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Product.
Require Import Theory.CartesianStrongMonoidal.

Generalizable All Variables.

Section CUT_NT.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} {F : Functor 𝒞 𝒟} `{!CartesianStrongMonoidal F}
          {E : 𝒞} (T : RelativeComonadWithCut F E).


  (** Functor 𝑻 : 𝒞 → 𝒟 **)
  Notation 𝑻 := (Lift(T)).

  Program Definition T_Ex : Functor 𝒞 𝒟 :=
    Functor.make
      (λ A ∙ T (E × A))
      (λ A B ∙ λ f ↦ T⋅cobind (T⋅extend (F⋅f ∘ T⋅counit))).
  Next Obligation. (* map-cong *)
    intros f g eq_fg. now rewrite eq_fg.
  Qed.
  Next Obligation. (* map-id *)
    rewrite <- identity, left_id, cut_counit.
    symmetry. etransitivity.
    apply Π.cong. apply Π₂.cong; [ reflexivity |].
    symmetry. apply ∘-×.
    rewrite <- compose_assoc, iso_right, left_id. apply cobind_counit.
  Qed.
  Next Obligation. (* map-compose *)
    symmetry. rewrite cobind_cobind. repeat rewrite compose_assoc.
    apply Π.cong. apply Π₂.cong ; [ reflexivity |].
    rewrite ∘-×, compose_assoc, counit_cobind.
    rewrite <- compose_assoc, Fπ₁_φ_inv, π₁_compose.
    rewrite cut_counit. repeat rewrite compose_assoc.
    rewrite counit_cobind. setoid_rewrite <- compose_assoc at 2.
    now rewrite Fπ₂_φ_inv, π₂_compose, map_compose, <- compose_assoc.
  Qed.


  Notation "'𝑻(𝑬×─)'" := T_Ex (at level 0).

  Program Definition 𝑪𝒖𝒕 : NaturalTransformation 𝑻(𝑬×─) 𝑻 :=
    NaturalTransformation.make (λ A ∙ T⋅cut).
  Next Obligation.
    rewrite cut_cobind. unfold Extend. simpl. reflexivity.
  Qed.

End CUT_NT.



