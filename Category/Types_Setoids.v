(**

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

(** 

  Content of this file:
  
  definition of the functor [EQ] from sets to setoids, proof that it is strong monoidal

*)

Require Import Category.Types.
Require Import Category.Setoids.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.Product.
Require Import Theory.Isomorphism.
Require Import Theory.CartesianStrongMonoidal.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＥＱ
  ----------------------------------------------------------------------------*)

Program Definition F : 𝑻𝒚𝒑𝒆 → 𝑺𝒆𝒕𝒐𝒊𝒅 := λ T ∙ Setoids.make T eq.

Program Definition map {A B} : [ A ⇒ B ⟶ F A ⇒ F B ] :=
  λ f ↦ Setoids.Morphism.make f.
Next Obligation.
  intros f g eq_fg x y eq_xy; simpl.
  now rewrite eq_xy.
Qed.

Definition id A : id[ F A ] ≈ map id[ A ].
Proof.
  intros x y eq_xy; now rewrite eq_xy.
Qed.

Definition map_compose A B C (f : A ⇒ B) (g : B ⇒ C) : map (g ∘ f) ≈ (map g) ∘ (map f).
Proof.
  intros x y eq_xy. now rewrite eq_xy.
Qed.

Definition 𝑬𝑸 : Functor 𝑻𝒚𝒑𝒆 𝑺𝒆𝒕𝒐𝒊𝒅 := mkFunctor id map_compose.


(*------------------------------------------------------------------------------
  -- ＥＱ  ＩＳ  ＳＴＲＯＮＧ  ＭＯＮＯＩＤＡＬ
  ----------------------------------------------------------------------------*)

Program Instance 𝑬𝑸_SM : CartesianStrongMonoidal 𝑬𝑸 :=
  CartesianStrongMonoidal.make (λ A B ∙ Setoids.Morphism.make (λ x ∙ x)).
Next Obligation.
  now f_equal.
Qed.
Next Obligation.
  constructor.
  - (* iso_left *)
    intros f g eq_fg. exact eq_fg.
  - (* iso_right *)
    intros f g eq_fg. simpl in *. destruct f. auto.
Qed.
