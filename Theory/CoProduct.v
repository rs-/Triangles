(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  - definition of universal property of product
  - some lemmas about interplay of product morphism with composition

*)

Require Import Theory.Category.
Require Import Theory.Product.

Generalizable All Variables.

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＣＯＰＲＯＤＵＣＴ  ＯＦ  ＯＢＪＥＣＴＳ
  ----------------------------------------------------------------------------*)
(** * Coproduct of object **)

(** ** Definition of universal property of coproduct (obtained by duality) **)

Definition Coproduct {𝒞 : Category} (A B : 𝒞) : Type := @Product (𝒞^op) A B.

Definition Cp_obj {𝒞 : Category} {A B : 𝒞} (Cp : Coproduct A B) : 𝒞 := AxB Cp.
Coercion Cp_obj : Coproduct >-> Obj.

Definition Cpmor {𝒞 : Category} {A B : 𝒞} {Cp : Coproduct A B}
  {C : 𝒞} : [ A ⇒ C ⟶ B ⇒ C ⟶ Cp_obj Cp ⇒ C ] := @Pmor _ _ _ Cp C.
Notation "[ f , g ]" := (Cpmor f g).

Section injections.
  Context {𝒞 : Category} {A B : 𝒞} (Cp : Coproduct A B).

  Notation "A+B" := (Cp_obj Cp).

  Definition ι₁ : A ⇒ A+B := @π₁ _ _ _ Cp.
  Definition ι₂ : B ⇒ A+B := @π₂ _ _ _ Cp.

  Lemma ι₁_compose : ∀ {C : 𝒞} {f : A ⇒ C} {g : B ⇒ C}, [ f , g ] ∘ ι₁ ≈ f.
  Proof. refine (@π₁_compose _ _ _ Cp). Qed.
  Lemma ι₂_compose : ∀ {C : 𝒞} {f : A ⇒ C} {g : B ⇒ C}, [ f , g ] ∘ ι₂ ≈ g.
  Proof. refine (@π₂_compose _ _ _ Cp). Qed.

  Lemma Cpmor_universal : ∀ {C : 𝒞} {f : A ⇒ C} {g : B ⇒ C} {i : A+B ⇒ C},
      i ∘ ι₁ ≈ f → i ∘ ι₂ ≈ g → i ≈ [ f , g ].
  Proof. refine (@Pmor_universal _ _ _ Cp). Qed.

End injections.

Arguments ι₁ {_ _ _ _}.
Arguments ι₂ {_ _ _ _}.


Definition mkCoproduct {𝒞 : Category} {A B} (AB : 𝒞) : ∀ (Cpmor : ∀ C : 𝒞, [A ⇒ C ⟶ B ⇒ C ⟶ AB ⇒ C])
(ι₁ : A ⇒ AB) (ι₂ : B ⇒ AB),
(∀ (C : 𝒞) (f : A ⇒ C) (g : B ⇒ C), (Cpmor C) f g ∘ ι₁ ≈ f)
→ (∀ (C : 𝒞) (f : A ⇒ C) (g : B ⇒ C), (Cpmor C) f g ∘ ι₂ ≈ g)
  → (∀ (C : 𝒞) (f : A ⇒ C) (g : B ⇒ C) (i : AB ⇒ C),
     i ∘ ι₁ ≈ f → i ∘ ι₂ ≈ g → i ≈ (Cpmor C) f g) → Coproduct A B.
Proof. refine (@mkProduct (𝒞^op) A B AB). Defined.

Notation "P '⋅ι₁'" := (@ι₁ _ _ _ P) (at level 0, only parsing).
Notation "P '⋅ι₂'" := (@ι₂ _ _ _ P) (at level 0, only parsing).
Notation "'ι₁[' A , B ]" := (ι₁ (A := A) (B := B)) (only parsing).
Notation "'ι₂[' A , B ]" := (ι₂ (A := A) (B := B)) (only parsing).

(*------------------------------------------------------------------------------
  -- ＨＡＳ  ＢＩＮＡＲＹ  ＣＯＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** ** Category has binary coproduct **)

Class BinaryCoproduct (𝒞 : Category) :=
  coproduct : ∀ (A B : 𝒞), Coproduct A B.
Typeclasses Opaque Coproduct.

Infix "⊎" := coproduct (at level 30).

Notation "'BinaryCoproduct.make' ⦃ 'Category' ≔ 𝒞 ; '_+_' ≔ cpr ; '[_,_]' ≔ cprm ; 'ι₁' ≔ inj1 ; 'ι₂' ≔ inj2 ⦄" :=
  (λ (A B : 𝒞) ∙ @mkCoproduct _ A B (cpr A B) (λ C ∙ Π₂.make (cprm C)) inj1 inj2 _ _ _) (only parsing).

(*------------------------------------------------------------------------------
  -- ＣＯＰＲＯＤＵＣＴ  ＬＡＷＳ
  ----------------------------------------------------------------------------*)

(** ** Laws on coproduct **)

Program Definition coprod_on_arrow
        `{BinaryCoproduct 𝒞} {A A' B B'} : [ A ⇒ A' ⟶ B ⇒ B' ⟶ A ⊎ B ⇒ A' ⊎ B' ] :=
  λ f g ↦₂ [ ι₁ ∘ f , ι₂ ∘ g ].
Next Obligation. cong₂; cong₂; intuition. Qed.

Infix "-⊎-" := coprod_on_arrow (at level 35).

Lemma coproduct_precompose `{BinaryCoproduct 𝒞} {A B C C' : 𝒞} {f : C ⇒ B} {g : C' ⇒ B} {p : B ⇒ A} :
    p ∘ [ f , g ] ≈ [ p ∘ f , p ∘ g ]    :> C ⊎ C' ⇒ A.
Proof.
  refine (@product_postcompose (𝒞^op) H _ _ _ _ f g p).
Qed.

Lemma coproduct_postcompose `{BinaryCoproduct 𝒞} {A B C D E : 𝒞}
      {f : D ⇒ B} {g : E ⇒ C} {h : B ⇒ A} {k : C ⇒ A} : [ h , k ] ∘ f-⊎-g ≈ [ h ∘ f , k ∘ g ]    :> D ⊎ E ⇒ A.
Proof.
  refine (@product_precompose (𝒞^op) H _ _ _ _ _ f g h k).
Qed.

Notation "∘-⊎" := coproduct_postcompose (only parsing).
Notation "⊎-∘" := coproduct_precompose  (only parsing).

Lemma coproduct_eta `{BinaryCoproduct 𝒞} {A B : 𝒞} : [ ι₁ , ι₂ ] ≈ id :> A ⊎ B ⇒ A ⊎ B.
Proof.
  sym; apply Cpmor_universal; apply Category.left_id.
Qed.

Lemma coproduct_arrow_id `{BinaryCoproduct 𝒞} {A B : 𝒞} : id -⊎- id ≈ id :> A ⊎ B ⇒ A ⊎ B.
Proof.
  simpl. sym; apply Cpmor_universal.
  - etrans. apply left_id. rew right_id.
  - etrans. apply left_id. rew right_id.
Qed.