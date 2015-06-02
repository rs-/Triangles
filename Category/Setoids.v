(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of the category of setoids

*)

Require Import Theory.Category.
Require Import Theory.Product.

Set Universe Polymorphism.

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

Program Definition compose {A B C} : [ B ⇒ C ⟶ A ⇒ B ⟶ A ⇒ C ] :=
  λ g f ↦₂ Π.make (λ x ∙ g (f x)).
(** g-cong **)
Next Obligation.
  now do 2 cong.
Qed.
(** g-cong₂ **)
Next Obligation.
  etrans. cong. apply H0. intuition.
Qed.

Local Infix "∘" := compose.

Lemma left_id A B (f : A ⇒ B) : id ∘ f ≈ f.
Proof.
  intros x; simpl. refl.
Qed.

Lemma right_id A B (f : A ⇒ B) : f ∘ id ≈ f.
Proof.
  intros x; refl.
Qed.

Lemma compose_assoc A B C D (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D) : h ∘ g ∘ f ≈ h ∘ (g ∘ f).
Proof.
  intros x; refl.
Qed.

Canonical Structure 𝑺𝒆𝒕𝒐𝒊𝒅 : Category :=
  mkCategory left_id right_id compose_assoc.


(*------------------------------------------------------------------------------
  -- ＳＥＴＯＩＤＳ  ＨＡＶＥ  ＢＩＮＡＲＹ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** ** Setoids have binary product **)

Section Product_construction.

  Program Definition product (A B : 𝑺𝒆𝒕𝒐𝒊𝒅) : 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    Setoid.make  ⦃ Carrier  ≔ A ⟨×⟩ B
                  ; Equiv    ≔ λ S₁ S₂ ∙ fst S₁ ≈ fst S₂ ∧ snd S₁ ≈ snd S₂ ⦄.
  (** equivalence **)
  Next Obligation.
    constructor; hnf.
    - intros [a  b]; split; refl.
    - intros [x y] [x' y'] [eq_xx' eq_yy']; split; now sym.
    - intros [x y] [x' y'] [x'' y''] [eq_xx' eq_yy'] [eq_x'x'' eq_y'y''];
      split; etrans; eauto.
  Qed.

  Program Definition product_mor (A B C : 𝑺𝒆𝒕𝒐𝒊𝒅) (f : C ⇒ A) (g : C ⇒ B) : C ⇒ product A B :=
    Π.make (λ c ∙ (f c , g c)).
  (** -,- cong **)
  Next Obligation.
    split; now cong.
  Qed.

  Program Definition proj_l {A B} : product A B ⇒ A := Π.make fst.

  Program Definition proj_r {A B} : product A B ⇒ B := Π.make snd.

End Product_construction.


Program Instance 𝑺𝒆𝒕𝒐𝒊𝒅_BinaryProduct : BinaryProduct 𝑺𝒆𝒕𝒐𝒊𝒅 :=
  BinaryProduct.make  ⦃ Category  ≔ 𝑺𝒆𝒕𝒐𝒊𝒅
                      ; _×_       ≔ product
                      ; ⟨_,_⟩     ≔ @product_mor _ _
                      ; π₁        ≔ proj_l
                      ; π₂        ≔ proj_r ⦄.
(** Pmor-cong₂ **)
Next Obligation.
  refl.
Qed.
(** π₁-cong **)
Next Obligation.
  refl.
Qed.
