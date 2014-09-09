(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of the category of relative comonads with cut

*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Product.
Require Import Theory.ProductPreservingFunctor.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤＳ  ＷＩＴＨ  ＣＵＴ
  ----------------------------------------------------------------------------*)
(** * Category of Relative comonads with cut **)

(** ** Category definition **)

Section Definitions.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          (F : Functor 𝒞 𝒟) (E : 𝒞) `{!ProductPreservingFunctor F}.

  Implicit Types (A B C D : RelativeComonadWithCut F E).

  Import RelativeComonadWithCut.Morphism.

  Infix "⇒" := Hom.
  Infix "∘" := compose.

  Lemma left_id A B  (f : A ⇒ B) : id ∘ f ≈ f.
  Proof.
    intro x; simpl. rewrite left_id. reflexivity.
  Qed.

  Lemma right_id A B (f : A ⇒ B) : f ∘ id ≈ f.
  Proof.
    intro x; simpl. now rewrite right_id.
  Qed.

  Lemma compose_assoc A B C D (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D) : h ∘ g ∘ f ≈ h ∘ (g ∘ f).
  Proof.
    intro x; simpl. now rewrite compose_assoc.
  Qed.

  Canonical Structure 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝒕 : Category :=
    mkCategory left_id right_id compose_assoc.

End Definitions.
