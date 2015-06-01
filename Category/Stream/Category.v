Set Printing Universes.


Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.PushforwardComodule.
Require Import Theory.Comodule.
Require Import Category.Types.
Require Import Category.Setoids.
Require Import Category.Types_Setoids.
Require Import Category.RComonad.
Require Import Category.RComod.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＳＴＲＥＡＭＳ
  ----------------------------------------------------------------------------*)
(** * Category of streams **)

(** ** Object and morphism definitions **)
Module Stream.

  Structure Obj : Type := mkObj
  { T         :>  𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 𝑬𝑸
  ; tail      :> [T] ⇒ [T] }.

  Arguments mkObj     {_ } _.
  Arguments T         _.
  Arguments tail      _.

  Notation "'Stream.make' ⦃ 'T' ≔ T ; 'tail' ≔ tail ⦄" :=
           (@mkObj T tail) (only parsing).

  Structure Morphism (T S : Obj) : Type := mkMorphism
  { τ           :> T ⇒ S
  ; τ_commutes  : ⟨τ⟩ ∘ τ⁎⋅T ≈ S ∘ ⟨τ⟩ }.

  Arguments mkMorphism  {_ _ _} _.
  Arguments τ           {_ _} _.
  Arguments τ_commutes  {_ _} _ {_ _ _ _}.

  Notation "'Stream.make' ⦃ 'τ' ≔ τ ⦄" := (@mkMorphism _ _ τ _) (only parsing).

  Program Definition Hom (T S : Obj) : Setoid :=
    Setoid.make   ⦃ Carrier  ≔ Morphism T S
                  ; Equiv    ≔ (λ g f ∙ g ≈ f) ⦄.
  (** equivalence **)
  Next Obligation.
    constructor.
    - repeat intro. now rewrite H.
    - repeat intro. symmetry; now rewrite H.
    - repeat intro; etransitivity; eauto. now apply H0.
  Qed.

End Stream.

Export Stream.

(** ** Identity and compositon definitions **)

Section Defs.

  Implicit Types (T S R U : Obj).

  Infix "⇒" := Hom.

  Program Definition id {T} : T ⇒ T :=
    Stream.make ⦃ τ ≔ id[T] ⦄.
  (** τ-cong **)
  Next Obligation.
    now rewrite H.
  Qed.

  Obligation Tactic := idtac.
  Program Definition compose {T S R} : [ S ⇒ R ⟶ T ⇒ S ⟶ T ⇒ R ] :=
    λ g f ↦₂ Stream.make ⦃ τ ≔ g ∘ f ⦄.
  (** τ-commutes **)
  Next Obligation.
    intros T S R g f.
    destruct g as [g g_commutes]. simpl in g_commutes.
    destruct f as [f f_commutes]. simpl in f_commutes. simpl.
    intros.
    rewrite H.
    etransitivity.
    eapply Setoids.cong.
    apply f_commutes.
    reflexivity.
    apply g_commutes.
    reflexivity.
  Qed.
  (** τ-proper **)
  Next Obligation.
    repeat intro.
    simpl.
    etransitivity. eapply Setoids.cong.
    eapply Setoids.cong. apply H1.
    etransitivity. eapply Setoids.cong.
    apply H0. reflexivity.
    apply H.
    reflexivity.
  Qed.

  Infix "∘" := compose.

  Lemma left_id : ∀ T S (f : T ⇒ S), id ∘ f ≈ f.
  Proof.
    intros. simpl. intros. rewrite H.
    reflexivity.
  Qed.

  Lemma right_id : ∀ T S (f : T ⇒ S), f ∘ id ≈ f.
  Proof.
    repeat intro. simpl. now rewrite H.
  Qed.

  Lemma compose_assoc T R S U (f : T ⇒ R) (g : R ⇒ S) (h : S ⇒ U) : h ∘ g ∘ f ≈ h ∘ (g ∘ f).
  Proof.
    repeat intro.
    simpl. now rewrite H.
  Qed.

  Canonical Structure 𝑺𝒕𝒓𝒆𝒂𝒎 : Category :=
    mkCategory left_id right_id compose_assoc.

End Defs.
