(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of functor

*)

Require Import Theory.Category.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)
(** ** Functor definition **)

Structure Functor (𝒞 𝒟 : Category) : Type := mkFunctor
{ F           :> 𝒞 → 𝒟
; map         : ∀ {A B}, [ A ⇒ B ⟶ F A ⇒ F B ]
; identity    : ∀ {A}, id[ F A ] ≈ map id[ A ]
; map_compose : ∀ {A B C} {f : A ⇒ B} {g : B ⇒ C}, map (g ∘ f) ≈ (map g) ∘ (map f) }.

Arguments mkFunctor {_ _} {_ _} _ _.
Arguments map       {_ _} _ {_ _}.

Notation "F ⋅ f" := (map F f) (at level 35, no associativity).

Notation "'Functor.make' ⦃ 'F' ≔ F ; 'map' ≔ map ⦄" :=
  (@mkFunctor _ _ F map _ _) (only parsing).
