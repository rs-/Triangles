Require Import Theory.Category.
Require Import Theory.Functor.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- Ｆ-ＣＯＡＬＧＥＢＲＡ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Structure CoAlgebra {𝒞 : Category} (F : Functor 𝒞 𝒞) : Type := mkCoAlgebra
{ A :> 𝒞
; α :> A ⇒ F A }.

Arguments mkCoAlgebra  {_ _} _ _.
Arguments α            {_ _} _.

Notation "'CoAlgebra.make' ⦃ 'A' ≔ A ; 'α' ≔ α  ⦄" := (@mkCoAlgebra _ _ A α) (only parsing).

Structure Morphism {𝒞} `{F : Functor 𝒞 𝒞} (α β : CoAlgebra F) : Type := mkMorphism
{ τ           :> α ⇒ β
; τ_commutes  : β ∘ τ ≈ F⋅τ ∘ α }.

Arguments mkMorphism  {_ _ _ _ _} _.
Arguments τ           {_ _ _ _} _.
Arguments τ_commutes  {_ _ _ _} _.

Notation "'CoAlgebra.make' ⦃ 'τ' ≔ τ ⦄" := (@mkMorphism _ _ _ _ τ _) (only parsing).

(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

Module Morphism.

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Section id_composition.

    Context {𝒞} `{F : Functor 𝒞 𝒞}.

    Implicit Types (α β γ : CoAlgebra F).

    Program Definition Hom α β : Setoid :=
      Setoid.make ⦃ Carrier ≔ Morphism α β ; Equiv ≔ λ f g ∙ f ≈ g ⦄.
    Next Obligation.
      constructor.
      - intros f; reflexivity.
      - intros f g eq_fg. symmetry. apply eq_fg.
      - intros f g h eq_fg eq_gh; etransitivity; eauto.
    Qed.

    Local Infix "⇒" := Hom.

    Program Definition id {α} : α ⇒ α :=
      CoAlgebra.make ⦃ τ ≔ id ⦄.
    Next Obligation.
      rewrite right_id. rewrite <- Functor.identity. rewrite left_id.
      reflexivity.
    Qed.

    Program Definition compose {α β γ} : [ β ⇒ γ ⟶ α ⇒ β ⟶ α ⇒ γ ] :=
      λ g f ↦₂ CoAlgebra.make ⦃ τ ≔ g ∘ f ⦄.
    Next Obligation.
      rewrite <- compose_assoc. rewrite map_compose.
      repeat rewrite compose_assoc. rewrite <- τ_commutes.
      repeat rewrite <- compose_assoc. rewrite <- τ_commutes.
      reflexivity.
    Qed.
    Next Obligation.
      intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂. simpl; now rewrite eq_f₁f₂, eq_g₁g₂.
    Qed.

  End id_composition.

End Morphism.