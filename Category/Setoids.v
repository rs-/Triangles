(*

   Benedikt Ahrens and Régis Spadotti

   Coinitial semantics for redecoration of triangular matrices

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of the category of setoids

*)

Require Import Theory.Category.
Require Import Theory.Product.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＳＥＴＯＩＤＳ
  ----------------------------------------------------------------------------*)
(** * Category of Setoids **)

(** In this file, we define the category of Setoids and show that this category has binary product.

    Note that to avoid universe inconsistancies we duplicate the definition of Setoid used to define
    the type of categories. **)

(** ** Setoid category definition **)

Module Setoids.

  Structure Obj := mkObj
  { SCarrier  :> Type
  ; SEquiv    : SCarrier → SCarrier → Prop
  ; is_SEquiv : Equivalence SEquiv }.

  Arguments mkObj  {_ _} _.
  Arguments SEquiv {_} _ _.

  Notation "'Setoids.make' ⦃ 'Carrier' ≔ c ; 'Equiv' ≔ eq ⦄" :=
    (@mkObj c eq _) (only parsing).

  Existing Instance is_SEquiv.

  Structure Morphism (A B : Obj) := mkMorphism
  { map  :> A → B
  ; cong : ∀ {x y}, SEquiv x y → SEquiv (map x) (map y) }.

  Instance map_Proper : ∀ A B (f : Morphism A B), Proper (SEquiv ==> SEquiv) (map A B f).
  Proof.
    intros A B f x y eq_xy.
    now apply cong.
  Qed.

  Arguments mkMorphism {_ _ _} _.
  Arguments map        {_ _} _ _.
  Arguments cong       {_ _} _ {_ _ _}.

  Module Morphism.

    Notation make map := (@mkMorphism _ _ map _) (only parsing).

  End Morphism.

  Program Definition Hom (A B : Obj) : Setoid :=
    Setoid.make ⦃ Carrier ≔ Morphism A B
                ; Equiv   ≔ λ f g ∙ ∀ x y, SEquiv x y → SEquiv (f x) (g y) ⦄.
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

Export Setoids.

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


(*------------------------------------------------------------------------------
  -- ＳＥＴＯＩＤＳ  ＨＡＶＥ  ＢＩＮＡＲＹ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** ** Setoids have binary product **)

Section Product_construction.

  Infix "∼" := SEquiv (at level 70).

  Program Definition product (A B : 𝑺𝒆𝒕𝒐𝒊𝒅) : 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    Setoids.make ⦃ Carrier ≔ A ⟨×⟩ B
                 ; Equiv   ≔ λ S₁ S₂ ∙ fst S₁ ∼ fst S₂ ∧ snd S₁ ∼ snd S₂ ⦄.
  Next Obligation.
    constructor; hnf.
    - intros [a  b]; split; reflexivity.
    - intros [x y] [x' y'] [eq_xx' eq_yy']; split; now symmetry.
    - intros [x y] [x' y'] [x'' y''] [eq_xx' eq_yy'] [eq_x'x'' eq_y'y''];
      split; etransitivity; eauto.
  Qed.

  Program Definition product_mor (A B C : 𝑺𝒆𝒕𝒐𝒊𝒅) (f : C ⇒ A) (g : C ⇒ B) : C ⇒ product A B :=
    Setoids.Morphism.make (λ c ∙ (f c , g c)).
  Next Obligation.
    split; now apply cong.
  Qed.

  Program Definition proj_l {A B} : product A B ⇒ A := Setoids.Morphism.make fst.

  Program Definition proj_r {A B} : product A B ⇒ B := Setoids.Morphism.make snd.

End Product_construction.


Program Instance 𝑺𝒆𝒕𝒐𝒊𝒅_BinaryProduct : BinaryProduct 𝑺𝒆𝒕𝒐𝒊𝒅 :=
  BinaryProduct.make ⦃ Category ≔ 𝑺𝒆𝒕𝒐𝒊𝒅
                     ; _×_      ≔ product
                     ; ⟨_,_⟩    ≔ @product_mor _ _
                     ; π₁       ≔ proj_l
                     ; π₂       ≔ proj_r ⦄.
Next Obligation. (* Pmor_cong₂ *)
  intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x y eq_xy; simpl; split.
  - now apply eq_f₁f₂.
  - now apply eq_g₁g₂.
Qed.
Next Obligation.
  now apply cong.
Qed.
Next Obligation.
  now apply cong.
Qed.
