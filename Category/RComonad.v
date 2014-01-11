(**

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤＳ
  ----------------------------------------------------------------------------*)

Section Definitions.

  Context `(F : Functor 𝒞 𝒟).

  Implicit Types (A B C D : RelativeComonad F).

  Import RelativeComonad.Morphism.

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

  Canonical Structure 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 : Category :=
    mkCategory left_id right_id compose_assoc.

End Definitions.
