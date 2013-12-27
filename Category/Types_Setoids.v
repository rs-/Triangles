Require Import Category.Types.
Require Import Category.Setoids.
Require Import Theory.Category.
Require Import Theory.Functor.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＥＱ
  ----------------------------------------------------------------------------*)

Program Definition F : 𝑻𝒚𝒑𝒆 → 𝑺𝒆𝒕𝒐𝒊𝒅 := λ T ∙ Setoids.make T eq.

Program Definition map {A B} : [ A ⇒ B ⟶ F A ⇒ F B ] :=
  λ f ↦ Setoids.Morphism.make f.
Next Obligation.
  intros f g eq_fg x y eq_xy; simpl.
  now rewrite eq_xy.
Qed.

Definition id A : id[ F A ] ≈ map id[ A ].
Proof.
  intros x y eq_xy; now rewrite eq_xy.
Qed.

Definition map_compose A B C (f : A ⇒ B) (g : B ⇒ C) : map (g ∘ f) ≈ (map g) ∘ (map f).
Proof.
  intros x y eq_xy. now rewrite eq_xy.
Qed.

Definition 𝑬𝑸 : Functor 𝑻𝒚𝒑𝒆 𝑺𝒆𝒕𝒐𝒊𝒅 := mkFunctor id map_compose.
