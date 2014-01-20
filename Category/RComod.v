(*

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:
  
  definition of the category of comodules over a fixed comonad towards a fixed category

*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＣＯＭＯＤＵＬＥＳ
  ----------------------------------------------------------------------------*)
(** * Category of Comodules **)

(** ** Category definition **)

Section Definitions.

  Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category).

  Implicit Types (A B C D : Comodule T ℰ).

  Import Comodule.Morphism.

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

  Canonical Structure 𝑹𝑪𝒐𝒎𝒐𝒅 : Category :=
    mkCategory left_id right_id compose_assoc.

End Definitions.
