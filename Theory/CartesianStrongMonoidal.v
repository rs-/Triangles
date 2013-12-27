Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.Product.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＲＴＥＳＩＡＮ  ＳＴＲＯＮＧ  ＭＯＮＯＩＤＡＬ  ＦＵＮＣＴＯＲ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Section StrongMonoidal.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞 𝒟).

  Definition φ (A B : 𝒞) : F (A × B) ⇒ F A × F B := ⟨ F ⋅ π₁ , F ⋅ π₂ ⟩.

  Class CartesianStrongMonoidal := mkCartesianStrongMonoidal
  { φ_inv        : ∀ {A B}, F A × F B ⇒ F (A × B)
  ; φ_is_inverse :> ∀ {A B}, IsInverse (φ A B) φ_inv }.

End StrongMonoidal.

Arguments mkCartesianStrongMonoidal {_ _ _ _ _ _} _.
Arguments φ {_ _ _ _ _ _ _}.

Notation make φ := (@mkCartesianStrongMonoidal _ _ _ _ _ φ _) (only parsing).