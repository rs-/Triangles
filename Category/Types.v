(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of the category of sets, proof that it has products

*)

Require Import Theory.Category.
Require Import Theory.Product.

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＴＹＰＥＳ
  ----------------------------------------------------------------------------*)
(** * Category of Types **)

(** ** Type category definition **)

Program Definition Hom (A B : Type) : Setoid := Setoid.make ⦃ Carrier ≔ A → B
                                                           ; Equiv   ≔ λ f g ∙ ∀ x, peq (f x) (g x) ⦄.
(** equivalence **)
Next Obligation.
  constructor; hnf; simpl; intros.
  - apply peq_refl.
  - destruct (H x0). apply peq_refl.
  - destruct (H0 x0). intuition.
Qed.

Local Infix "⇒" := Hom.

Definition id {A} : A ⇒ A := λ x ∙ x.

Program Definition compose {A B C} : [ B ⇒ C ⟶ A ⇒ B ⟶ A ⇒ C ] :=
  Π₂.make (λ g f x ∙ g (f x)).
(** g-cong₂ **)
Next Obligation.
  destruct (H0 x0). intuition.
Qed.

Local Infix "∘" := compose.

Lemma left_id A B (f : A ⇒ B) : id ∘ f ≈ f.
Proof.
  hnf ; intuition.
Qed.

Lemma right_id A B (f : A ⇒ B) : f ∘ id ≈ f.
Proof.
  hnf ; intuition.
Qed.

Lemma compose_assoc A B C D (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D) : h ∘ g ∘ f ≈ h ∘ (g ∘ f).
Proof.
  hnf ; intuition.
Qed.

Canonical Structure 𝑻𝒚𝒑𝒆 : Category :=
  mkCategory left_id right_id compose_assoc.

(*------------------------------------------------------------------------------
  -- ＴＹＰＥＳ  ＨＡＶＥ  ＢＩＮＡＲＹ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** ** Types have binary product **)

Program Instance 𝑻𝒚𝒑𝒆_BinaryProduct : BinaryProduct 𝑻𝒚𝒑𝒆 :=
  BinaryProduct.make  ⦃ Category  ≔ 𝑻𝒚𝒑𝒆
                      ; _×_       ≔ _⟨×⟩_
                      ; ⟨_,_⟩     ≔ λ C f g (c : C) ∙ (f c , g c)
                      ; π₁        ≔ fst
                      ; π₂        ≔ snd ⦄.
(** Pmor-cong₂ **)
Next Obligation.
  destruct (H0 x0). destruct (H x0). apply peq_refl.
Qed.
(** Pmor-universal **)
Next Obligation.
  apply peq_refl.
Qed.
Next Obligation.
  apply peq_refl.
Qed.
Next Obligation.
  destruct (H x), (H0 x), (i x). apply peq_refl.
Qed.
