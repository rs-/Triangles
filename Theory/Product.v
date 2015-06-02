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

Generalizable All Variables.

Set Universe Polymorphism.


(*------------------------------------------------------------------------------
  -- ＰＲＯＤＵＣＴ  ＯＦ  ＯＢＪＥＣＴＳ
  ----------------------------------------------------------------------------*)
(** * Product of object **)

(** ** Definition of universal property of product **)

Structure Product {𝒞 : Category} (A B : 𝒞) : Type := mkProduct
{ AxB            :> 𝒞
; Pmor           : ∀ {C : 𝒞}, [ C ⇒ A ⟶ C ⇒ B ⟶ C ⇒ AxB ] where "⟨ f , g ⟩" := (Pmor f g)
; π₁             : AxB ⇒ A
; π₂             : AxB ⇒ B
; π₁_compose     : ∀ {C : 𝒞} {f : C ⇒ A} {g : C ⇒ B}, π₁ ∘ ⟨ f , g ⟩ ≈ f
; π₂_compose     : ∀ {C : 𝒞} {f : C ⇒ A} {g : C ⇒ B}, π₂ ∘ ⟨ f , g ⟩ ≈ g
; Pmor_universal : ∀ {C : 𝒞} {f : C ⇒ A} {g : C ⇒ B} {i : C ⇒ AxB},
                     π₁ ∘ i ≈ f → π₂ ∘ i ≈ g → i ≈ ⟨ f , g ⟩ }.

Arguments mkProduct {_ _ _ _ _ _ _} _ _ _.
Arguments AxB       {_ _ _} _.
Arguments Pmor      {_ _ _} {_ _}.
Arguments π₁        {_ _ _ _}.
Arguments π₂        {_ _ _ _}.

Notation "⟨ f , g ⟩" := (Pmor f g).
Notation "P '⋅π₁'" := (π₁ (p := P)) (at level 0, only parsing).
Notation "P '⋅π₂'" := (π₂ (p := P)) (at level 0, only parsing).
Notation "'π₁[' A , B ]" := (π₁ (A := A) (B := B)) (only parsing).
Notation "'π₂[' A , B ]" := (π₂ (A := A) (B := B)) (only parsing).

(*------------------------------------------------------------------------------
  -- ＨＡＳ  ＢＩＮＡＲＹ  ＰＲＯＤＵＣＴ
  ----------------------------------------------------------------------------*)
(** ** Category has binary product **)

Class BinaryProduct (𝒞 : Category) :=
  product : ∀ (A B : 𝒞), Product A B.

Infix "×" := product (at level 20).

Notation "'BinaryProduct.make' ⦃ 'Category' ≔ 𝒞 ; '_×_' ≔ pr ; '⟨_,_⟩' ≔ prm ; 'π₁' ≔ pr1 ; 'π₂' ≔ pr2 ⦄" :=
  (λ (A B : 𝒞) ∙ @mkProduct _ A B (pr A B) (λ C ∙ Π₂.make (prm C)) pr1 pr2 _ _ _) (only parsing).


(*------------------------------------------------------------------------------
  -- ＰＲＯＤＵＣＴ  ＬＡＷＳ
  ----------------------------------------------------------------------------*)

(** ** Laws on product **)

Program Definition prod_on_arrow
        `{BinaryProduct 𝒞} {A A' B B'} : [ A ⇒ A' ⟶ B ⇒ B' ⟶ A × B ⇒ A' × B' ] :=
  λ f g ↦₂ ⟨ f ∘ π₁ , g ∘ π₂ ⟩.
Next Obligation.
  cong₂; cong₂; intuition.
Qed.

Infix "-×-" := prod_on_arrow (at level 35).

Lemma product_postcompose `{BinaryProduct 𝒞} {A B C C' : 𝒞} {f : B ⇒ C} {g : B ⇒ C'} {p : A ⇒ B} :
   ⟨ f , g ⟩ ∘ p ≈ ⟨ f ∘ p , g ∘ p ⟩    :> A ⇒ C × C'.
Proof.
  apply Pmor_universal.
  - etrans; [ rew compose_assoc|]. cong_l; apply π₁_compose.
  - etrans; [ rew compose_assoc|]. cong_l; apply π₂_compose.
Qed.

Lemma product_precompose `{BinaryProduct 𝒞} {A B C D E : 𝒞}
      {f : B ⇒ D} {g : C ⇒ E} {h : A ⇒ B} {k : A ⇒ C} : f-×-g ∘ ⟨ h , k ⟩ ≈ ⟨ f ∘ h , g ∘ k ⟩    :> A ⇒ D × E.
Proof.
  apply Pmor_universal.
  - etrans; [ rew compose_assoc |]. etrans. cong_l. apply π₁_compose. etrans. rew compose_assoc.
    cong_r. apply π₁_compose.
  - etrans; [ rew compose_assoc |]. etrans. cong_l. apply π₂_compose. etrans. rew compose_assoc.
    cong_r. apply π₂_compose.
Qed.

Notation "∘-×" := product_postcompose (only parsing).
Notation "×-∘" := product_precompose  (only parsing).
