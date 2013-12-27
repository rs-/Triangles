Require Import Theory.Category.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＳＥＴＯＩＤＳ
  ----------------------------------------------------------------------------*)

Module Setoids.

  Structure Obj := mkObj
  { SCarrier  :> Type
  ; SEquiv    : SCarrier → SCarrier → Prop
  ; is_SEquiv : Equivalence SEquiv }.

  Arguments mkObj  {_ _} _.
  Arguments SEquiv {_} _ _.

  Notation make c eq := (@mkObj c eq _) (only parsing).

  Local Existing Instance is_SEquiv.

  Structure Morphism (A B : Obj) := mkMorphism
  { map  :> A → B
  ; cong : ∀ {x y}, SEquiv x y → SEquiv (map x) (map y) }.

  Arguments mkMorphism {_ _ _} _.

  Module Morphism.

    Notation make map := (@mkMorphism _ _ map _) (only parsing).

  End Morphism.

  Program Definition Hom (A B : Obj) : Setoid :=
    Setoid.make (Morphism A B) (λ f g ∙ ∀ x y, SEquiv x y → SEquiv (f x) (g y)).
  Next Obligation.
    constructor.
    - intros f x y eq_xy. now apply cong.
    - intros f g eq_fg x y eq_xy.
      etransitivity; [ apply cong; apply eq_xy | ].
      symmetry; now apply eq_fg.
    - intros f g h eq_fg eq_gh x y eq_xy.
      etransitivity; eauto. now apply eq_gh.
  Qed.

End Setoids.

Import Setoids.

Local Infix "⇒" := Hom.

Program Definition id {A} : A ⇒ A := Setoids.Morphism.make (λ x ∙ x).

Program Definition compose {A B C} : [ B ⇒ C ⟶ A ⇒ B ⟶ A ⇒ C ] :=
  λ g f ↦₂ Setoids.Morphism.make (λ x ∙ g (f x)).
Next Obligation.
  now do 2 apply cong.
Qed.
Next Obligation.
  intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x y eq_xy; simpl.
  now apply eq_f₁f₂, eq_g₁g₂.
Qed.

Local Infix "∘" := compose.

Lemma left_id A B (f : A ⇒ B) : id ∘ f ≈ f.
Proof.
  intros x y eq_xy; simpl; now apply cong.
Qed.

Lemma right_id A B (f : A ⇒ B) : f ∘ id ≈ f.
Proof.
  intros x y eq_xy; simpl; now apply cong.
Qed.

Lemma compose_assoc A B C D (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D) : h ∘ g ∘ f ≈ h ∘ (g ∘ f).
  intros x y eq_xy; simpl; now repeat apply cong.
Qed.

Canonical Structure 𝑺𝒆𝒕𝒐𝒊𝒅 : Category :=
  mkCategory left_id right_id compose_assoc.