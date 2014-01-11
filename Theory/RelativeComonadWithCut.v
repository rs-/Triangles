(**

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

(** 

  Content of this file:
  
  - definition of comonad with cut
  - definition of morphisms of comonads with cut, identity, composition

*)

Require Import Category.RComonad.
Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.CartesianStrongMonoidal.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ  ＷＩＴＨ  ＣＵＴ
  ----------------------------------------------------------------------------*)

Section Defs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          (F : Functor 𝒞 𝒟) (E : 𝒞) `{!CartesianStrongMonoidal F}.

  Section ExtendConstruction.

    Context {T : RelativeComonad F}
            (cut : ∀ A, T (E × A) ⇒ T A).

    Program Definition Extend {A B} : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
      λ f ↦ φ⁻¹ ∘ ⟨ F ⋅ π₁ ∘ T⋅counit , f ∘ cut A ⟩.
    Next Obligation.
      intros f g eq_fg. now rewrite eq_fg.
    Qed.

  End ExtendConstruction.

  Structure RelativeComonadWithCut := mkRelativeComonadWithCut
  { T          :> RelativeComonad F
  ; cut        : ∀ {A}, T (E × A) ⇒ T A
  ; cut_counit : ∀ {A}, T⋅counit[A] ∘ cut ≈ F ⋅ π₂ ∘ T⋅counit
  ; cut_cobind : ∀ {A B} {f : T A ⇒ F B}, T⋅cobind(f) ∘ cut ≈ cut ∘ T⋅cobind (Extend (@cut) f) }.

  Definition extend {T : RelativeComonadWithCut} {A B} : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
    Extend (@cut T).

End Defs.

Arguments RelativeComonadWithCut   {_ _ _ _} _ _ {_}.
Arguments mkRelativeComonadWithCut {_ _ _ _ _ _ _ _ _} _ _.
Arguments T                        {_ _ _ _ _ _ _} _.
Arguments cut                      {_ _ _ _ _ _ _} _ {_}.
Arguments cut_counit               {_ _ _ _ _ _ _} _ {_}.
Arguments cut_cobind               {_ _ _ _ _ _ _} _ {_ _ _}.
Arguments extend                   {_ _ _ _ _ _ _} _ {_ _}.

Notation "'cut[' X ]" := (cut _ (A := X)) (only parsing).
Notation "T '⋅cut'" := (cut T) (at level 0).
Notation "T '⋅cut[' X ]" := (cut T (A := X)) (at level 0, only parsing).

Notation "T '⋅extend'" := (extend T) (at level 0).

Notation make T cut :=
  (@mkRelativeComonadWithCut _ _ _ _ _ _ _ T cut _ _) (only parsing).
Notation Make T counit cobind cut :=
  (@mkRelativeComonadWithCut _ _ _ _ _ _ _ (RelativeComonad.make T counit cobind) cut _ _) (only parsing).

(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

Section MDefs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          {F : Functor 𝒞 𝒟} {E : 𝒞} `{!CartesianStrongMonoidal F}.

  Local Notation "[ R ]" := (T R) (only parsing).

  Structure Morphism (T S : RelativeComonadWithCut F E) : Type := mkMorphism
  { τ     :> [T] ⇒ [S]
  ; τ_cut : ∀ {A}, S⋅cut ∘ τ(E × A) ≈ τ(A) ∘ T⋅cut }.

End MDefs.

Arguments mkMorphism {_ _ _ _ _ _ _ _ _ _} _.
Arguments τ          {_ _ _ _ _ _ _ _ _} _.
Arguments τ_cut      {_ _ _ _ _ _ _ _ _} _ {_}.

Module Morphism.

  Notation make τ := (@mkMorphism _ _ _ _ _ _ _ _ _ τ _) (only parsing).
  Notation Make τ := (@mkMorphism _ _ _ _ _ _ _ _ _ (RelativeComonad.Morphism.make τ) _) (only parsing).

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Section id_composition.

    Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
            {F : Functor 𝒞 𝒟} {E : 𝒞} `{!CartesianStrongMonoidal F}.

    Implicit Types (T S U : RelativeComonadWithCut F E).

    Program Definition Hom T S : Setoid :=
      Setoid.make (Morphism T S) _≈_.
    Next Obligation.
      constructor.
      - intros f x; reflexivity.
      - intros f g eq_fg x. symmetry. apply eq_fg.
      - intros f g h eq_fg eq_gh; etransitivity; eauto.
    Qed.

    Local Infix "⇒" := Hom.

    Program Definition id {S} : S ⇒ S :=
      make id.
    Next Obligation.
      now rewrite left_id, right_id.
    Qed.

    Program Definition compose {S T U} : [ T ⇒ U ⟶ S ⇒ T ⟶ S ⇒ U ] :=
      λ g f ↦₂ make (g ∘ f).
    Next Obligation.
      rewrite compose_assoc. rewrite <- τ_cut. repeat rewrite <- compose_assoc.
      now rewrite τ_cut.
    Qed.
    Next Obligation.
      intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x.
      apply Π₂.cong; [ apply eq_f₁f₂ | apply eq_g₁g₂ ].
    Qed.

  End id_composition.

End Morphism.