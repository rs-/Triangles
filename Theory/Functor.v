Require Import Theory.Category.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Structure Functor (𝒞 𝒟 : Category) : Type := mkFunctor
{ F           :> 𝒞 → 𝒟
; map         : ∀ {A B}, [ A ⇒ B ⟶ F A ⇒ F B ]
; identity    : ∀ {A}, id[ F A ] ≈ map id[ A ]
; map_compose : ∀ {A B C} {f : A ⇒ B} {g : B ⇒ C}, map (g ∘ f) ≈ (map g) ∘ (map f) }.

Arguments mkFunctor {_ _} {_ _} _ _.
Arguments map       {_ _} _ {_ _}.

Notation "F ⋅ f" := (map F f) (at level 35, no associativity).

Notation make F map := (@mkFunctor _ _ F map _ _).