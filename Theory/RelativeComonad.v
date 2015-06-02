(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  - definition of relative comonad
  - relative comonads are functors
  - definition of morphisms of comonads, identity, composition

*)

Require Import Theory.Category.
Require Import Theory.Functor.

Generalizable All Variables.

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)
(** * Relative comonad **)

(** ** Definition **)

Structure RelativeComonad `(F : Functor 𝒞 𝒟) : Type := mkRelativeComonad
{ T              :>  𝒞 → 𝒟
; counit         :   ∀ {X}, T X ⇒ F X
; cobind         :   ∀ {X Y}, [ T X ⇒ F Y ⟶ T X ⇒ T Y ]
; cobind_counit  :   ∀ {X}, cobind counit ≈ id[ T X ]
; counit_cobind  :   ∀ {X Y} {f : T X ⇒ F Y}, counit ∘ cobind(f) ≈ f
; cobind_cobind  :   ∀ {X Y Z} {f : T X ⇒ F Y} {g : T Y ⇒ F Z}, cobind(g) ∘ cobind(f) ≈ cobind(g ∘ cobind(f)) }.

Arguments mkRelativeComonad  {_ _ _ _ _ _} _ _ _.
Arguments counit             {_ _ _} _ {_}.
Arguments cobind             {_ _ _} _ {_ _}.
Arguments cobind_counit      {_ _ _} _ {_}.
Arguments counit_cobind      {_ _ _} _ {_ _ _}.
Arguments cobind_cobind      {_ _ _} _ {_ _ _ _ _}.

Notation "'counit[' X ]"     := (counit _ (X := X)) (only parsing).
Notation "T '⋅counit'"       := (counit T) (at level 0, only parsing).
Notation "T '⋅counit[' X ]"  := (counit T (X := X)) (at level 0, only parsing).
Notation "T '⋅cobind'"       := (cobind T) (at level 0, only parsing).

Notation "'RelativeComonad.make' ⦃ 'T' ≔ T ; 'counit' ≔ counit ; 'cobind' ≔ cobind ⦄" :=
  (@mkRelativeComonad _ _ _ T counit cobind _ _ _) (only parsing).

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲＩＡＬＩＴＹ
  ----------------------------------------------------------------------------*)
(** ** Functoriality of relative comonads **)

(* begin hide *)
Section Functoriality.
(* end hide *)

  Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F).

  Program Definition lift {A B} : [ A ⇒ B ⟶ T A ⇒ T B ] :=
    λ f ↦ T⋅cobind (F⋅f ∘ T⋅counit).
  Next Obligation.
    cong. cong_l. now cong.
  Qed.

  Lemma lift_id : ∀ A, id[ T A ] ≈ lift id[ A ].
  Proof.
    intros A; simpl; unfold lift.
    etrans. sym. apply cobind_counit.
    cong. sym. etrans. cong_l. sym. apply identity.
    apply left_id.
  Qed.

  Lemma lift_compose : ∀ A B C (f : A ⇒ B) (g : B ⇒ C), lift (g ∘ f) ≈ (lift g) ∘ (lift f).
  Proof.
    intros A B C g f; simpl; unfold lift.
    sym. etrans. apply cobind_cobind.
    cong. sym. etrans. cong_l. apply map_compose.
    etrans. apply compose_assoc.
    sym. etrans. apply compose_assoc.
    cong_r. etrans. apply counit_cobind.
    refl.
  Qed.

  Definition Lift : Functor 𝒞 𝒟 := mkFunctor lift_id lift_compose.

(* begin hide *)
End Functoriality.
(* end hide *)


(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)
(** ** Morphism of relative comonads **)

Structure Morphism `{F : Functor 𝒞 𝒟} (T S : RelativeComonad F) : Type := mkMorphism
{ τ           :>  ∀ C, T C ⇒ S C
; τ_counit    :   ∀ {C}, T⋅counit[ C ] ≈ S⋅counit[ C ] ∘ τ(C)
; τ_commutes  :   ∀ {C D} {f : S C ⇒ F D}, τ(D) ∘ T⋅cobind (f ∘ τ(C)) ≈ S⋅cobind f ∘ τ(C) }.

Arguments mkMorphism  {_ _ _ _ _ _} _ _.
Arguments τ           {_ _ _ _ _ _} _.
Arguments τ_counit    {_ _ _ _ _} _ {_}.
Arguments τ_commutes  {_ _ _ _ _} _ {_ _ _}.

Notation "'RelativeComonad.make' ⦃ 'τ' ≔ τ ⦄" := (@mkMorphism _ _ _ _ _ τ _ _) (only parsing).

Module Morphism.

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Section id_composition.

    Context `{F : Functor 𝒞 𝒟}.

    Implicit Types (T S U : RelativeComonad F).

    Program Definition Hom T S : Setoid :=
      Setoid.make ⦃ Carrier ≔ Morphism T S ; Equiv ≔ λ f g ∙ ∀ x, f x ≈ g x ⦄.
    Next Obligation.
      constructor.
      - intros f x; refl.
      - intros f g eq_fg x. now sym.
      - intros f g h eq_fg eq_gh x; etrans; eauto.
    Qed.

    Local Infix "⇒" := Hom.

    Unset Printing Universes.

    Program Definition id {S} : S ⇒ S :=
      RelativeComonad.make ⦃ τ ≔ λ C ∙ id[ S C ] ⦄.
    Next Obligation.
      sym; apply right_id.
    Qed.
    Next Obligation.
      etrans. apply left_id.
      etrans. cong. apply right_id.
      sym. apply right_id.
    Qed.

    Program Definition compose {S T U} : [ T ⇒ U ⟶ S ⇒ T ⟶ S ⇒ U ] :=
      λ g f ↦₂ RelativeComonad.make ⦃ τ ≔ λ C ∙ g(C) ∘ f(C) ⦄.
    Next Obligation.
      etrans; [| apply compose_assoc].
      sym. etrans; [cong_l|]; rew @τ_counit.
    Qed.
    Next Obligation.
      etrans; [| apply compose_assoc].
      etrans; [| cong_l; apply τ_commutes].
      etrans; [ apply compose_assoc |].
      etrans; [| rew compose_assoc].
      cong_r. etrans. cong_r. cong. rew compose_assoc.
      etrans. apply τ_commutes. refl.
    Qed.
    Next Obligation.
      cong₂; intuition.
    Qed.

  End id_composition.

End Morphism.
