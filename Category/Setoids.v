(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of the category of setoids

*)

Set Universe Polymorphism.

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

Local Infix "⇒" := setoid.

Program Definition id {A} : A ⇒ A := Π.make (λ x ∙ x).
Next Obligation. solve_proper. Qed.

Program Definition compose {A B C} : [ B ⇒ C ⟶ A ⇒ B ⟶ A ⇒ C ] :=
  λ g f ↦₂ Π.make (λ x ∙ g (f x)).
(** g-cong **)
Next Obligation. solve_proper. Qed.
(** g-cong₂ **)
Next Obligation.
  intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x y eq_xy; simpl.
  now apply eq_f₁f₂, eq_g₁g₂.
Qed.

Local Infix "∘" := compose.

Lemma left_id A B (f : A ⇒ B) : id ∘ f ≈ f.
Proof.
  intros x y eq_xy; simpl. now rewrite eq_xy.
Qed.

Lemma right_id A B (f : A ⇒ B) : f ∘ id ≈ f.
Proof.
  intros x y eq_xy; simpl; now rewrite eq_xy.
Qed.

Lemma compose_assoc A B C D (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D) : h ∘ g ∘ f ≈ h ∘ (g ∘ f).
Proof.
  intros x y eq_xy; simpl. now rewrite eq_xy.
Qed.

Canonical Structure 𝑺𝒆𝒕𝒐𝒊𝒅 : Category :=
  mkCategory left_id right_id compose_assoc.


(*------------------------------------------------------------------------------
  -- ＳＥＴＯＩＤＳ  ＨＡＶＥ  ＢＩＮＡＲＹ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** ** Setoids have binary product **)

Section Product_construction.

  Infix "∼" := _≈_ (at level 70).

  Program Definition product (A B : 𝑺𝒆𝒕𝒐𝒊𝒅) : 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    Setoid.make  ⦃ Carrier  ≔ A ⟨×⟩ B
                 ; Equiv    ≔ λ S₁ S₂ ∙ fst S₁ ∼ fst S₂ ∧ snd S₁ ∼ snd S₂ ⦄.
  (** equivalence **)
  Next Obligation.
    constructor; hnf.
    - intros [a  b]; split; reflexivity.
    - intros [x y] [x' y'] [eq_xx' eq_yy']; split; now symmetry.
    - intros [x y] [x' y'] [x'' y''] [eq_xx' eq_yy'] [eq_x'x'' eq_y'y''];
      split; etransitivity; eauto.
  Qed.

  Program Definition product_mor (A B C : 𝑺𝒆𝒕𝒐𝒊𝒅) (f : C ⇒ A) (g : C ⇒ B) : C ⇒ product A B :=
    Π.make (λ c ∙ (f c , g c)).
  (** -,- cong **)
  Next Obligation.
    split; now apply Π.cong.
  Qed.

  Program Definition proj_l {A B} : product A B ⇒ A := Π.make fst.
  Next Obligation. repeat intro; intuition. Qed.

  Program Definition proj_r {A B} : product A B ⇒ B := Π.make snd.
  Next Obligation. repeat intro; intuition. Qed.

End Product_construction.


Program Instance 𝑺𝒆𝒕𝒐𝒊𝒅_BinaryProduct : BinaryProduct 𝑺𝒆𝒕𝒐𝒊𝒅 :=
  BinaryProduct.make  ⦃ Category  ≔ 𝑺𝒆𝒕𝒐𝒊𝒅
                      ; _×_       ≔ product
                      ; ⟨_,_⟩     ≔ @product_mor _ _
                      ; π₁        ≔ proj_l
                      ; π₂        ≔ proj_r ⦄.
(** Pmor-cong₂ **)
Next Obligation.
  intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x y eq_xy; simpl; split.
  - now apply eq_f₁f₂.
  - now apply eq_g₁g₂.
Qed.
(** π₁-cong **)
Next Obligation.
  now apply Π.cong.
Qed.
(** π₂-cong **)
Next Obligation.
  now apply Π.cong.
Qed.
