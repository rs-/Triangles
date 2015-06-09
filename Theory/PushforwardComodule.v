(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  - definition of pushforward of comodules along a comonad morphism
  - definition of comodule morphism induced by a comonad morphism
  - commutativity of pushforward with precomposition w. product

*)

(* Require Import Category.RComonad. *)
Require Import Category.RComod.
(* Require Import Category.RComonadWithCut. *)
Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.ProductPreservingFunctor.
Require Import Theory.PrecompositionWithProduct.

Generalizable All Variables.

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＰＵＳＨＦＯＲＷＡＲＤ  ＣＯＭＯＤＵＬＥ
  ----------------------------------------------------------------------------*)
(** * Pushforward comodule **)

(** ** Definition **)
Section Pushforward_construction.

  Context `{F : Functor 𝒞 𝒟} {T S : RelativeComonad F}
           (τ : RelativeComonad.Morphism.Hom T S) `(M : Comodule T ℰ).

  Program Definition pushforward : Comodule S ℰ :=
    Comodule.make  ⦃ M        ≔ M
                   ; mcobind  ≔ λ C D ∙ λ f ↦ M⋅mcobind (f ∘ τ(C)) ⦄.
  Next Obligation. (* mcobind_cong *)
    cong. now cong_l.
  Qed.
  Next Obligation. (* mcobind_counit *)
    etrans. cong. sym. apply τ_counit.
    apply mcobind_counit.
  Qed.
  Next Obligation. (* mcobind_mcobind *)
    etrans; [| cong; etrans; [| rew compose_assoc]; cong_r; rew @τ_commutes ].
    etrans. apply mcobind_mcobind. cong. apply compose_assoc.
  Qed.

End Pushforward_construction.

(*------------------------------------------------------------------------------
  -- ＦＵNＣＴＯＲＩＡＬＩＴＹ
  ----------------------------------------------------------------------------*)
(** ** Functoriality of pushforward **)

Section Functoriality.

  Context `{F : Functor 𝒞 𝒟} {T S : RelativeComonad F} {ℰ : Category} {M N : Comodule S ℰ}
          (τ : RelativeComonad.Morphism.Hom S T) (α : Comodule.Morphism.Hom M N).

  Infix "⁎" := pushforward (at level 0).

  Program Definition pushforward_mor : ‵ Comodule.Morphism.Hom τ⁎M τ⁎N ′ :=
    Comodule.make ⦃ α ≔ α ⦄.
  Next Obligation. (* α_commutes *)
    apply α_commutes.
  Qed.

End Functoriality.

Definition Pushforward
        `{F : Functor 𝒞 𝒟} {T S : RelativeComonad F}
        (τ : RelativeComonad.Morphism.Hom T S) {ℰ} : Functor (𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ) (𝑹𝑪𝒐𝒎𝒐𝒅 S ℰ).
  refine (Functor.make  ⦃ F    ≔ pushforward τ
                ; map  ≔ λ A B ∙ λ f ↦ pushforward_mor τ f ⦄).
  intros; intros ?; apply H.
  repeat intro; refl.
  repeat intro; refl.
Defined.

Notation "τ ⁎" := (pushforward τ) (at level 0).

(** ** Tautological comodule **)
Section tautological_comodule.

  Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F).

  Program Definition tcomod : Comodule T 𝒟 :=
    Comodule.make  ⦃ M        ≔ T
                   ; mcobind  ≔ λ C D ∙ T⋅cobind ⦄.
  (** mcobind-counit *)
  Next Obligation.
    apply cobind_counit.
  Qed.
  (** mcobind-mcobind *)
  Next Obligation.
    apply cobind_cobind.
  Qed.

End tautological_comodule.

Local Coercion tcomod : RelativeComonad >-> Comodule.
Notation "[ T ]" := (tcomod T) (only parsing).

(** ** Induced morphism **)

Section induced_morphism.

  Context `{F : Functor 𝒞 𝒟} {T S : RelativeComonad F}
          (τ : RelativeComonad.Morphism.Hom T S).

  Definition induced_morphism : Comodule.Morphism.Hom (τ⁎T) S.
  Proof.
    refine (@Comodule.mkMorphism _ _ _ _ _ _ _ _ _).
    - intros C. apply τ.
    - intros. apply τ_commutes.
  Defined.

End induced_morphism.

Notation "⟨ τ ⟩" := (induced_morphism τ) (at level 0).

Section Commutes.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} {F : Functor 𝒞 𝒟}
          {E : 𝒞} `{!ProductPreservingFunctor F} {T S : RelativeComonadWithCut F E}
          {τ : RelativeComonadWithCut.Morphism.Hom T S} `{M : Comodule T ℰ}.

  Program Definition Φ : ‵ Comodule.Morphism.Hom (τ⁎(M[E×─])) ((τ⁎M)[E×─]) ′ :=
    Comodule.make ⦃ α ≔ λ X ∙ id[M (E × X)] ⦄.
  Next Obligation.
    etrans. apply left_id. etrans; [| sym; apply right_id].
    cong. etrans; [|rew compose_assoc].
    cong_r. etrans; [| sym; apply ∘-×]. cong₂.
    etrans; [| rew compose_assoc]. cong₂; [refl|]. apply τ_counit.
    etrans; [| rew compose_assoc]. etrans. apply compose_assoc. cong₂; [ refl|].
    rew @τ_cut.
  Qed.

End Commutes.
