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
    intros x y eq_xy. now rewrite eq_xy.
  Qed.

  Lemma mlift_id A : id[ M A ] ≈ mlift id[ A ].
  Proof.
    simpl. rewrite <- identity, left_id, mcobind_counit.
    reflexivity.
  Qed.

  Lemma mlift_compose A B C (f : A ⇒ B) (g : B ⇒ C) : mlift (g ∘ f) ≈ (mlift g) ∘ (mlift f).
  Proof.
    simpl.
    rewrite mcobind_mcobind,
            compose_assoc,
            counit_cobind,
            <- compose_assoc,
            <- map_compose.
    reflexivity.
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

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Section id_composition.

    Context `{F : Functor 𝒞 𝒟} {T : RelativeComonad F} {ℰ : Category}.

    Program Definition Hom (M N : Comodule T ℰ) : Setoid :=
      Setoid.make ⦃ Carrier ≔ Morphism M N
                  ; Equiv   ≔ λ f g ∙ ∀ x, f x ≈ g x ⦄.
    Next Obligation.
      constructor.
      - intros f x; reflexivity.
      - intros f g eq_fg x. symmetry. apply eq_fg.
      - intros f g h eq_fg eq_gh; etransitivity; eauto.
    Qed.

    Local Infix "⇒" := Hom.

    Program Definition id {M : Comodule T ℰ} : M ⇒ M :=
      Comodule.make ⦃ α ≔ λ C ∙ id[ M C ] ⦄.
    Next Obligation.
      now rewrite left_id, right_id.
    Qed.

    Program Definition compose {M N P : Comodule T ℰ} : [ N ⇒ P ⟶ M ⇒ N ⟶ M ⇒ P ] :=
      λ g f ↦₂ Comodule.make ⦃ α ≔ λ C ∙ g(C) ∘ f(C) ⦄.
    Next Obligation.
      rewrite <- compose_assoc; rewrite <- α_commutes.
      rewrite compose_assoc; rewrite α_commutes; rewrite compose_assoc.
      reflexivity.
    Qed.
    Next Obligation.
      intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x. simpl.
      apply Π₂.cong; [ apply eq_f₁f₂ | apply eq_g₁g₂ ].
    Qed.

  End id_composition.

End Morphism.
