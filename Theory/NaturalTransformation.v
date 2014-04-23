(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of natural transformations

*)

Require Import Theory.Category.
Require Import Theory.Functor.

(*------------------------------------------------------------------------------
  -- ＮＡＴＵＲＡＬ  ＴＲＡＮＳＦＯＲＭＡＴＩＯＮ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)
(** * Natural transformation definition **)

Structure NaturalTransformation {𝒞 𝒟 : Category} (F G : Functor 𝒞 𝒟) := mkNaturalTransformation
{ η : ∀ A, F A ⇒ G A
; η_commutes : ∀ {A B} {f : A ⇒ B}, η(B) ∘ F ⋅ f ≈ G ⋅ f ∘ η(A) }.

Arguments mkNaturalTransformation {_ _ _ _ _} _.
Arguments η                       {_ _ _ _} _ _.
Arguments η_commutes              {_ _ _ _} _ {_ _ _}.

Notation "'NaturalTransformation.make' ⦃ 'η' ≔ η ⦄" :=
  (@mkNaturalTransformation _ _ _ _ η _) (only parsing).
