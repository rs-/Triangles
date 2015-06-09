(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  - definition of comonad with cut
  - definition of morphisms of comonads with cut, identity, composition

*)

(* Require Import Category.RComonad. *)
Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.ProductPreservingFunctor.

Generalizable All Variables.

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ  ＷＩＴＨ  ＣＵＴ
  ----------------------------------------------------------------------------*)
(** ** Relative comonad with cut **)


(** ** Definition **)

Section Defs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          (F : Functor 𝒞 𝒟) (E : 𝒞) `{!ProductPreservingFunctor F}.

  Section ExtendConstruction.

    Context {T : RelativeComonad F}
            (cut : ∀ A, T (E × A) ⇒ T A).

    Program Definition Extend {A B} : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
      λ f ↦ φ⁻¹ ∘ ⟨ F ⋅ π₁ ∘ T⋅counit , f ∘ cut A ⟩.
    Next Obligation.
      cong_r. cong_r. now cong_l.
    Qed.

  End ExtendConstruction.

  Structure RelativeComonadWithCut := mkRelativeComonadWithCut
  { T           :>  RelativeComonad F
  ; cut         :   ∀ {A}, T (E × A) ⇒ T A
  ; cut_counit  :   ∀ {A}, T⋅counit[A] ∘ cut ≈ F ⋅ π₂ ∘ T⋅counit
  ; cut_cobind  :   ∀ {A B} {f : T A ⇒ F B}, T⋅cobind(f) ∘ cut ≈ cut ∘ T⋅cobind (Extend (@cut) f) }.

  Definition extend {T : RelativeComonadWithCut} {A B} : [ T A ⇒ F B ⟶ T (E × A) ⇒ F (E × B) ] :=
    Extend (@cut T).

End Defs.

Arguments RelativeComonadWithCut    {_ _ _ _} _ _ {_}.
Arguments mkRelativeComonadWithCut  {_ _ _ _ _ _ _ _ _} _ _.
Arguments T                         {_ _ _ _ _ _ _} _.
Arguments cut                       {_ _ _ _ _ _ _} _ {_}.
Arguments cut_counit                {_ _ _ _ _ _ _} _ {_}.
Arguments cut_cobind                {_ _ _ _ _ _ _} _ {_ _ _}.
Arguments extend                    {_ _ _ _ _ _ _} _ {_ _}.

Notation "'cut[' X ]"     := (cut _ (A := X)) (only parsing).
Notation "T '⋅cut'"       := (cut T) (at level 0).
Notation "T '⋅cut[' X ]"  := (cut T (A := X)) (at level 0, only parsing).
Notation "T '⋅extend'"    := (extend T) (at level 0).

Notation "'RelativeComonadWithCut.make' ⦃ 'RelativeComonad' ≔ RelativeComonad ; 'cut' ≔ cut ⦄" :=
  (@mkRelativeComonadWithCut _ _ _ _ _ _ _ RelativeComonad cut _ _) (only parsing).
Notation "'RelativeComonadWithCut.make' ⦃ 'T' ≔ T ; 'counit' ≔ counit ; 'cobind' ≔ cobind ; 'cut' ≔ cut ⦄" :=
  (@mkRelativeComonadWithCut _ _ _ _ _ _ _
      (RelativeComonad.make ⦃ T ≔ T ;  counit ≔ counit ; cobind ≔ cobind ⦄ ) cut _ _) (only parsing).

(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

(** ** Morphism **)

Section MDefs.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          {F : Functor 𝒞 𝒟} {E : 𝒞} `{!ProductPreservingFunctor F}.

  Local Notation "[ R ]" := (T R) (only parsing).

  Structure Morphism (T S : RelativeComonadWithCut F E) : Type := mkMorphism
  { τ      :>  RelativeComonad.Morphism.Hom T S
  ; τ_cut  :   ∀ {A}, S⋅cut ∘ τ(E × A) ≈ τ(A) ∘ T⋅cut }.

End MDefs.

Arguments mkMorphism  {_ _ _ _ _ _ _ _ _ _} _.
Arguments τ           {_ _ _ _ _ _ _ _ _} _.
Arguments τ_cut       {_ _ _ _ _ _ _ _ _} _ {_}.

Notation "'RelativeComonadWithCut.make' ⦃ 'RelativeComonad-τ' ≔ τ ⦄" :=
  (@mkMorphism _ _ _ _ _ _ _ _ _ τ _) (only parsing).
Notation "'RelativeComonadWithCut.make' ⦃ 'τ' ≔ τ ⦄" :=
  (@mkMorphism _ _ _ _ _ _ _ _ _ (RelativeComonad.make ⦃ τ ≔ τ ⦄) _) (only parsing).

Module Morphism.

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Section id_composition.

    Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
            {F : Functor 𝒞 𝒟} {E : 𝒞} `{!ProductPreservingFunctor F}.

    Implicit Types (T S U : RelativeComonadWithCut F E).

    Program Definition Hom T S : Setoid :=
      Setoid.make  ⦃ Carrier  ≔ Morphism T S
                   ; Equiv    ≔ _≈_ ⦄.
    Next Obligation.
      constructor.
      - intros f x; refl.
      - intros f g eq_fg x. now sym.
      - intros f g h eq_fg eq_gh x; etrans; eauto.
    Qed.

    Local Infix "⇒" := Hom.

    Program Definition id {S} : S ⇒ S :=
      RelativeComonadWithCut.make ⦃ RelativeComonad-τ ≔ RelativeComonad.Morphism.id ⦄.
    Next Obligation.
      etrans. rew left_id. cong_r.
      rew right_id.
    Qed.

    Program Definition compose {S T U} : [ T ⇒ U ⟶ S ⇒ T ⟶ S ⇒ U ] :=
      λ g f ↦₂ RelativeComonadWithCut.make ⦃ RelativeComonad-τ ≔ RelativeComonad.Morphism.compose g f ⦄.
    Next Obligation.
      etrans. rew compose_assoc. etrans. cong_l. rew @τ_cut.
      etrans; [| rew compose_assoc]. etrans. rew compose_assoc.
      cong_r. rew @τ_cut.
    Qed.
    Next Obligation.
      cong₂; intuition.
    Qed.

  End id_composition.

End Morphism.

Section CanonicalCut.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟}
          {F : Functor 𝒞 𝒟} (E : 𝒞) `{!ProductPreservingFunctor F}.

  Program Definition ccut (R : RelativeComonad F) : RelativeComonadWithCut F E :=
    RelativeComonadWithCut.make ⦃ RelativeComonad ≔ R ; cut ≔ λ A ∙ lift R π₂[E,A] ⦄.
  Next Obligation.
    apply counit_cobind.
  Qed.
  Next Obligation.
    etrans. apply cobind_cobind.
    sym. etrans. apply cobind_cobind. sym.
    cong. etrans; [| rew compose_assoc].
    etrans; [| cong_r; sym; apply @counit_cobind].
    etrans; [| rew compose_assoc].
    etrans; [| cong_l; rew @Fπ₂_φ_inv ].
    etrans; [| sym; apply @π₂_compose ].
    refl.
  Qed.

End CanonicalCut.

Notation "↑[ R ]" := (ccut _ R).
Notation "↑[ R ; E ]" := (ccut E R).
