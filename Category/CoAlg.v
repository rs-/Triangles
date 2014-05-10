Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.CoAlgebra.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  Ｆ-ＣＯＡＬＧＥＢＲＡ
  ----------------------------------------------------------------------------*)
(** * Category of Comodules **)

(** ** Category definition **)

Section Definitions.

  Context {𝒞 : Category} (F : Functor 𝒞 𝒞).

  Implicit Types (α β γ δ : CoAlgebra F).

  Import CoAlgebra.Morphism.

  Infix "⇒" := Hom.
  Infix "∘" := compose.

  Lemma left_id α β (f : α ⇒ β) : id ∘ f ≈ f.
  Proof.
    simpl. now rewrite left_id.
  Qed.

  Lemma right_id α β (f : α ⇒ β) : f ∘ id ≈ f.
  Proof.
    simpl; now rewrite right_id.
  Qed.

  Lemma compose_assoc α β γ δ (f : α ⇒ β) (g : β ⇒ γ) (h : γ ⇒ δ) : h ∘ g ∘ f ≈ h ∘ (g ∘ f).
  Proof.
    simpl. now rewrite compose_assoc.
  Qed.

  Canonical Structure 𝑪𝒐𝑨𝒍𝒈 : Category :=
    mkCategory left_id right_id compose_assoc.

End Definitions.