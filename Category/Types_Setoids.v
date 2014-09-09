(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of the functor [EQ] from sets to setoids, proof that it is strong monoidal

*)

Require Import Category.Types.
Require Import Category.Setoids.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.Product.
Require Import Theory.Isomorphism.
Require Import Theory.ProductPreservingFunctor.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＥＱ
  ----------------------------------------------------------------------------*)
(** * Functor 𝑬𝑸 : 𝑻𝒚𝒑𝒆 → 𝑺𝒆𝒕𝒐𝒊𝒅 **)

(** ** Definition **)

Program Definition F : 𝑻𝒚𝒑𝒆 → 𝑺𝒆𝒕𝒐𝒊𝒅 := λ T ∙ Setoids.make  ⦃ Carrier  ≔ T
                                                            ; Equiv    ≔ eq ⦄.

Program Definition map {A B} : [ A ⇒ B ⟶ F A ⇒ F B ] :=
  λ f ↦ Setoids.Morphism.make f.
(** f-cong **)
Next Obligation.
  intros f g eq_fg x y eq_xy; simpl.
  now rewrite eq_xy.
Qed.

Lemma id A : id[ F A ] ≈ map id[ A ].
Proof.
  intros x y eq_xy; now rewrite eq_xy.
Qed.

Lemma map_compose A B C (f : A ⇒ B) (g : B ⇒ C) : map (g ∘ f) ≈ (map g) ∘ (map f).
Proof.
  intros x y eq_xy. now rewrite eq_xy.
Qed.

Definition 𝑬𝑸 : Functor 𝑻𝒚𝒑𝒆 𝑺𝒆𝒕𝒐𝒊𝒅 := mkFunctor id map_compose.


(*------------------------------------------------------------------------------
  -- ＥＱ  ＩＳ  ＰＲＥＳＥＶＥＳ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** ** 𝑬𝑸 is strong monoidal **)

Program Instance 𝑬𝑸_PF : ProductPreservingFunctor 𝑬𝑸 :=
  ProductPreservingFunctor.make ⦃ φ ≔ λ A B ∙ Setoids.Morphism.make (λ x ∙ x) ⦄.
(** φ-cong **)
Next Obligation.
  now f_equal.
Qed.
(** φ-inverse **)
Next Obligation.
  constructor.
  - (* iso_left *)
    intros f g eq_fg. exact eq_fg.
  - (* iso_right *)
    intros f g eq_fg. simpl in *. destruct f. auto.
Qed.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＥＱ-×
  ----------------------------------------------------------------------------*)
(** * Functor 𝑬𝑸-× : 𝑻𝒚𝒑𝒆 × 𝑻𝒚𝒑𝒆 → 𝑺𝒆𝒕𝒐𝒊𝒅 **)

(** ** Definition **)


Program Definition 𝑬𝑸_prod : Functor (𝑻𝒚𝒑𝒆 𝘅 𝑻𝒚𝒑𝒆) 𝑺𝒆𝒕𝒐𝒊𝒅 :=
  Functor.make ⦃ F   ≔ λ A ∙ Setoids.make ⦃ Carrier ≔ fst A ⟨×⟩ snd A
                                          ; Equiv ≔ eq ⦄
               ; map ≔ λ A B ∙ λ f ↦ Setoids.Morphism.make (λ x ∙ (fst f (fst x) , snd f (snd x))) ⦄.
(** equivalence **)
Next Obligation.
  eauto with typeclass_instances.
Qed.
(** map-proper **)
Next Obligation.
  intros [? ?] [? ?] [? ?] [? ?] [? ?] eq. injection eq; intros.
  simpl in *; f_equal; congruence.
Qed.

Notation "𝑬𝑸-𝘅" := 𝑬𝑸_prod.
