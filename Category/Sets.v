(*

   Benedikt Ahrens and Régis Spadotti

   Coinitial semantics for redecoration of triangular matrices

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of the category of sets, proof that it has products

*)

Require Import Theory.Category.
Require Import Theory.Product.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＳＥＴＳ
  ----------------------------------------------------------------------------*)
(** * Category of Sets **)

(** ** Type category definition **)

Definition Obj := Type.

Program Definition Hom (A B : Obj) : Setoid := Setoid.make ⦃ Carrier ≔ A → B
                                                           ; Equiv   ≔ λ f g ∙ ∀ x, f x = g x ⦄.
Next Obligation.
  constructor; hnf; simpl; [ reflexivity | now symmetry | etransitivity ; eauto ].
Qed.

Local Infix "⇒" := Hom.

Definition id {A} : A ⇒ A := λ x ∙ x.

Program Definition compose {A B C} : [ B ⇒ C ⟶ A ⇒ B ⟶ A ⇒ C ] :=
  Π₂.make (λ g f x ∙ g (f x)).
Next Obligation.
  intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x.
  now rewrite eq_f₁f₂, eq_g₁g₂.
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

Canonical Structure 𝑺𝒆𝒕 : Category :=
  mkCategory left_id right_id compose_assoc.


(*------------------------------------------------------------------------------
  -- ＳＥＴＳ  ＨＡＶＥ  ＢＩＮＡＲＹ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** ** Sets have binary product **)

Program Instance 𝑺𝒆𝒕_BinaryProduct : BinaryProduct 𝑺𝒆𝒕 :=
  BinaryProduct.make  ⦃ Category  ≔ 𝑺𝒆𝒕
                      ; _×_       ≔ _⟨×⟩_
                      ; ⟨_,_⟩     ≔ λ C f g (c : C) ∙ (f c , g c)
                      ; π₁        ≔ fst
                      ; π₂        ≔ snd ⦄.
Next Obligation. (* Pmor_cong₂ *)
  intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x. now f_equal.
Qed.
Next Obligation. (* Pmor_universal *)
  rewrite <- H. rewrite <- H0.
  remember (i x); destruct (i x); now subst.
Qed.
