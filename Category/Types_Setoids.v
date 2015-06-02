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

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＥＱ
  ----------------------------------------------------------------------------*)
(** * Functor 𝑬𝑸 : 𝑻𝒚𝒑𝒆 → 𝑺𝒆𝒕𝒐𝒊𝒅 **)

(** ** Definition **)

Program Definition F : 𝑻𝒚𝒑𝒆 → 𝑺𝒆𝒕𝒐𝒊𝒅 := λ T ∙ Setoid.make  ⦃ Carrier  ≔ T
                                                            ; Equiv    ≔ peq ⦄.
Next Obligation.
  constructor; hnf; intros.
  - apply peq_refl.
  - destruct H; apply peq_refl.
  - destruct H. assumption.
Qed.
Existing Instance F_obligation_1.


Program Definition map {A B} : [ A ⇒ B ⟶ F A ⇒ F B ] :=
  λ f ↦ Π.make f.
(** f-cong **)
Next Obligation.
  destruct H; apply peq_refl.
Qed.

Lemma id A : id[ F A ] ≈ map id[ A ].
Proof.
  intros x; apply peq_refl.
Qed.

Lemma map_compose A B C (f : A ⇒ B) (g : B ⇒ C) : map (g ∘ f) ≈ (map g) ∘ (map f).
Proof.
  intros x; apply peq_refl.
Qed.

Definition 𝑬𝑸 : Functor 𝑻𝒚𝒑𝒆 𝑺𝒆𝒕𝒐𝒊𝒅 := mkFunctor id map_compose.


(*------------------------------------------------------------------------------
  -- ＥＱ  ＩＳ  ＰＲＥＳＥＶＥＳ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** ** 𝑬𝑸 is strong monoidal **)

Program Instance 𝑬𝑸_PF : ProductPreservingFunctor 𝑬𝑸 :=
  ProductPreservingFunctor.make ⦃ φ ≔ λ A B ∙ Π.make (λ x ∙ x) ⦄.
(** φ-cong **)
Next Obligation.
  destruct x, y; simpl in *. destruct H, H0. apply peq_refl.
Qed.
(** φ-inverse **)
Next Obligation.
  constructor.
  - (* iso_left *)
    intros (?&?); simpl; split; apply peq_refl.
  - (* iso_right *)
    intros (?&?); simpl; split; apply peq_refl.
Qed.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＥＱ-×
  ----------------------------------------------------------------------------*)
(** * Functor 𝑬𝑸-× : 𝑻𝒚𝒑𝒆 × 𝑻𝒚𝒑𝒆 → 𝑺𝒆𝒕𝒐𝒊𝒅 **)

(** ** Definition **)


Program Definition 𝑬𝑸_prod : Functor (𝑻𝒚𝒑𝒆 𝘅 𝑻𝒚𝒑𝒆) 𝑺𝒆𝒕𝒐𝒊𝒅 :=
  Functor.make ⦃ F   ≔ λ A ∙ Setoid.make ⦃ Carrier ≔ fst A ⟨×⟩ snd A
                                          ; Equiv ≔ peq ⦄
               ; map ≔ λ A B ∙ λ f ↦ Π.make (λ x ∙ (fst f (fst x) , snd f (snd x))) ⦄.
(** equivalence **)
Next Obligation.
  destruct H. simpl. apply peq_refl.
Qed.
(** map-proper **)
Next Obligation.
  destruct x0; simpl in *. destruct (H f), (H0 s). apply peq_refl.
Qed.
Next Obligation.
  destruct x; apply peq_refl.
Qed.
Next Obligation.
  destruct x; apply peq_refl.
Qed.

Notation "𝑬𝑸-𝘅" := 𝑬𝑸_prod.
