(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  - definition of comodule over relative comonad
  - definition of morphisms of comodules, identity and composition

*)

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.

Generalizable All Variables.

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＣＯＭＯＤＵＬＥ  ＯＶＥＲ  ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)
(** ** Comodule over relative comonad definition **)

Structure Comodule `{F : Functor 𝒞 𝒟} (T : RelativeComonad F) (ℰ : Category) : Type := mkComodule
{ M                :>  𝒞 → ℰ
; mcobind          :   ∀ {C D}, [ T C ⇒ F D ⟶ M C ⇒ M D ]
; mcobind_counit   :   ∀ {C}, mcobind counit[ C ] ≈ id[ M C ]
; mcobind_mcobind  :   ∀ {C D E} {f : T C ⇒ F D} {g : T D ⇒ F E},
                         mcobind(g) ∘ mcobind(f) ≈ mcobind(g ∘ T⋅cobind(f)) }.

Arguments mkComodule       {_ _ _ _ _ _ _} _ _.
Arguments M                {_ _ _ _ _} _ _.
Arguments mcobind          {_ _ _ _ _} _ {_ _}.
Arguments mcobind_counit   {_ _ _ _ _} _ {_}.
Arguments mcobind_mcobind  {_ _ _ _ _} _ {_ _ _ _ _}.

Notation "M '⋅mcobind'" := (mcobind M) (at level 0).

Notation "'Comodule.make' ⦃ 'M' ≔ M ; 'mcobind' ≔ mcobind ⦄" :=
  (@mkComodule _ _ _ _ _ M mcobind _ _) (only parsing).

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲＩＡＬＩＴＹ
  ----------------------------------------------------------------------------*)
(** ** Functoriality of comodule **)

(* begin hide *)
Section Functoriality.
(* end hide *)

  Context `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ} (M : Comodule T ℰ).

  Program Definition mlift {A B} : [ A ⇒ B ⟶ M A ⇒ M B ] :=
    λ f ↦ M⋅mcobind (F⋅f ∘ counit[ A ]).
  Next Obligation.
    cong. cong_l. now cong.
  Qed.

  Lemma mlift_id A : id[ M A ] ≈ mlift id[ A ].
  Proof.
    simpl.
    etrans. sym. apply mcobind_counit.
    cong. sym. etrans. cong_l. sym. apply identity.
    apply left_id.
  Qed.

  Lemma mlift_compose A B C (f : A ⇒ B) (g : B ⇒ C) : mlift (g ∘ f) ≈ (mlift g) ∘ (mlift f).
  Proof.
    simpl.
    sym. etrans. apply mcobind_mcobind.
    cong. sym. etrans. cong_l. apply map_compose.
    etrans. apply compose_assoc.
    sym. etrans. apply compose_assoc.
    cong_r. etrans. apply counit_cobind.
    refl.
  Qed.

  Definition MLift : Functor 𝒞 ℰ := mkFunctor mlift_id mlift_compose.

(* begin hide *)
End Functoriality.
(* end hide *)


(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)
(** ** Morphism of comodules **)

Structure Morphism `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ} (M N : Comodule T ℰ) : Type := mkMorphism
{ α           :> ∀ C, M C ⇒ N C
; α_commutes  : ∀ {C D} {f : T C ⇒ F D}, α(D) ∘ M⋅mcobind f ≈ N⋅mcobind f ∘ α(C) }.

Arguments mkMorphism  {_ _ _ _ _ _ _ _} _.
Arguments α           {_ _ _ _ _ _ _} _ _.
Arguments α_commutes  {_ _ _ _ _ _ _} _ {_ _ _}.

Notation "'Comodule.make' ⦃ 'α' ≔ α ⦄" :=
         (@mkMorphism _ _ _ _ _ _ _ α _) (only parsing).

Module Morphism.

  Set Printing Universes.

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Section id_composition.

    Context `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ : Category}.

    Program Definition Hom (M N : Comodule T ℰ) : Setoid :=
      Setoid.make ⦃ Carrier ≔ Morphism M N
                  ; Equiv   ≔ λ f g ∙ ∀ x, f x ≈ g x ⦄.
    Next Obligation.
      constructor.
      - intros f x; refl.
      - intros f g eq_fg x. now sym.
      - intros f g h eq_fg eq_gh x; etrans; eauto.
    Qed.

    Local Infix "⇒" := Hom.

    Program Definition id {M : Comodule T ℰ} : M ⇒ M :=
      Comodule.make ⦃ α ≔ λ C ∙ id[ M C ] ⦄.
    Next Obligation.
      etrans. apply left_id. rew right_id.
    Qed.

    Program Definition compose {M N P : Comodule T ℰ} : [ N ⇒ P ⟶ M ⇒ N ⟶ M ⇒ P ] :=
      λ g f ↦₂ Comodule.make ⦃ α ≔ λ C ∙ g(C) ∘ f(C) ⦄.
    Next Obligation.
      etrans; [| apply compose_assoc].
      etrans; [| cong_l; apply α_commutes].
      etrans. rew compose_assoc.
      etrans. cong_r. apply α_commutes.
      etrans; [ rew compose_assoc|].
      refl.
    Qed.
    Next Obligation.
      cong₂; intuition.
    Qed.

  End id_composition.

End Morphism.
