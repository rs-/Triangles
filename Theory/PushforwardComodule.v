Require Import Category.RComonad.
Require Import Category.RComod.
Require Import Category.RComonadWithCut.
Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.CartesianStrongMonoidal.
Require Import Theory.ProductInContext.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＰＵＳＨＦＯＲＷＡＲＤ  ＣＯＭＯＤＵＬＥ
  ----------------------------------------------------------------------------*)

Section Pushforward_construction.

  Context `{F : Functor 𝒞 𝒟} {T S : RelativeComonad F}
           (τ : T ⇒ S) `(M : Comodule T ℰ).

  Program Definition pushforward : Comodule S ℰ :=
    Comodule.make M (λ C D ∙ λ f ↦ M⋅mcobind (f ∘ τ(C))).
  Next Obligation. (* mcobind_cong *)
    solve_proper.
  Qed.
  Next Obligation. (* mcobind_counit *)
    rewrite <- τ_counit. now rewrite mcobind_counit.
  Qed.
  Next Obligation. (* mcobind_compose *)
    now rewrite compose_assoc,
                <- τ_commutes,
                mcobind_compose,
                <- compose_assoc.
  Qed.

End Pushforward_construction.

(*------------------------------------------------------------------------------
  -- ＦＵNＣＴＯＲＩＡＬＩＴＹ
  ----------------------------------------------------------------------------*)

Section Functoriality.

  Context `{F : Functor 𝒞 𝒟} {T S : RelativeComonad F} {ℰ : Category} {M N : Comodule S ℰ}
          (τ : S ⇒ T) (α : M ⇒ N).

  Infix "⁎" := pushforward (at level 0).

  Program Definition pushforward_mor : τ⁎M ⇒ τ⁎N :=
    Comodule.Morphism.make α.
  Next Obligation. (* α_commutes *)
    now rewrite α_commutes.
  Qed.

End Functoriality.

Program Definition Pushforward
             `{F : Functor 𝒞 𝒟} {T S : RelativeComonad F} (τ : T ⇒ S) {ℰ} : Functor (𝑹𝑪𝒐𝒎𝒐𝒅 T ℰ) (𝑹𝑪𝒐𝒎𝒐𝒅 S ℰ) :=
  Functor.make (pushforward τ) (λ A B ∙ λ f ↦ pushforward_mor τ f).
Next Obligation.
  intros f g eq_fg x. simpl. now apply eq_fg.
Qed.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  reflexivity.
Qed.

Notation "τ ⁎" := (Pushforward τ) (at level 0).

Section tautological_comodule.

  Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F).

  Program Definition tcomod : Comodule T 𝒟 :=
    Comodule.make T (λ C D ∙ T⋅cobind).
  Next Obligation. (* mcobind_counit *)
    now rewrite cobind_counit.
  Qed.
  Next Obligation. (* mcobind_compose *)
    now rewrite cobind_compose.
  Qed.

End tautological_comodule.

Coercion tcomod : RelativeComonad >-> Comodule.
Notation "[ T ]" := (tcomod T) (only parsing).

Section induced_morphism.

  Context `{F : Functor 𝒞 𝒟} {T S : RelativeComonad F}
          (τ : T ⇒ S).

  Program Definition induced_morphism : τ⁎T ⇒ S :=
    Comodule.Morphism.make (λ C ∙ τ(C)).
  Next Obligation. (* α_commutes *)
    now rewrite τ_commutes.
  Qed.

End induced_morphism.

Notation "[ τ ']⁎'" := (induced_morphism τ) (at level 0).

Section Commutes.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} {F : Functor 𝒞 𝒟}
          {E : 𝒞} `{!CartesianStrongMonoidal F} {T S : RelativeComonadWithCut F E}
          {τ : T ⇒ S} `{M : Comodule T ℰ}.

  Program Definition Φ : τ⁎(M[E×─]) ⇒ (τ⁎M)[E×─] :=
    Comodule.Morphism.make (λ X ∙ id[M (E × X)]).
  Next Obligation.
    rewrite left_id, right_id.
    apply Π.cong.
    repeat rewrite compose_assoc.
    apply Π₂.cong; [ reflexivity |].
    rewrite ∘-×; apply Π₂.cong.
    rewrite compose_assoc; apply Π₂.cong; [ reflexivity |].
    apply τ_counit.
    rewrite compose_assoc. apply Π₂.cong; [ reflexivity |].
    symmetry. apply τ_cut.
  Qed.

End Commutes.