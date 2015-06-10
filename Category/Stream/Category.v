Require Import Category.Types.
Require Import Category.Setoids.
Require Import Category.Types_Setoids.
Require Import Category.RComonad.
Require Import Category.RComod.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.PushforwardComodule.
Require Import Theory.Comodule.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＳＴＲＥＡＭＳ
  ----------------------------------------------------------------------------*)
(** * Category of streams **)

(** ** Object and morphism definitions **)
Module Stream.

  Structure Obj : Type := mkObj
  { T         :> RelativeComonad 𝑬𝑸
  ; tail      : Comodule.Morphism [T] [T] }.

  Arguments mkObj     {_ } _.
  Arguments T         _.
  Arguments tail      _.

  Notation "'Stream.make' ⦃ 'T' ≔ T ; 'tail' ≔ tail ⦄" :=
           (@mkObj T tail) (only parsing).

  Structure Morphism (T S : Obj) : Type := mkMorphism
  { τ           :> RelativeComonad.Morphism T S
  ; τ_commutes  : Comodule.Morphism.compose ⟨τ⟩ (pushforward_mor τ (tail T)) ≈ Comodule.Morphism.compose (tail S) ⟨τ⟩ }.

  Arguments mkMorphism  {_ _ _} _.
  Arguments τ           {_ _} _.
  Arguments τ_commutes  {_ _} _ {_ _}.

  Notation "'Stream.make' ⦃ 'τ' ≔ τ ⦄" := (@mkMorphism _ _ τ _) (only parsing).

  Program Definition Hom (T S : Obj) : Setoid :=
    Setoid.make   ⦃ Carrier  ≔ Morphism T S
                  ; Equiv    ≔ (λ g f ∙ ∀ x, g x ≈ f x) ⦄.
  (** equivalence **)
  Next Obligation.
    constructor.
    - repeat intro. refl.
    - repeat intro. sym; apply H.
    - repeat intro; etrans; eauto.
  Qed.

End Stream.

Export Stream.

(** ** Identity and compositon definitions **)

Section Defs.

  Implicit Types (T S R U : Obj).

  Infix "⇒" := Hom.

  Program Definition id {T} :T ⇒ T :=
    Stream.make ⦃ τ ≔ RelativeComonad.Morphism.id ⦄.
  (** τ-cong **)
  Next Obligation.
    refl.
  Qed.

  Obligation Tactic := idtac.
  Program Definition compose {T S R} : [ S ⇒ R ⟶ T ⇒ S ⟶ T ⇒ R ] :=
    λ g f ↦₂ Stream.make ⦃ τ ≔ RelativeComonad.Morphism.compose g f ⦄.
  (** τ-commutes **)
  Next Obligation.
    intros T S R g f.
    destruct g as [g g_commutes]. simpl in g_commutes.
    destruct f as [f f_commutes]. simpl in f_commutes. simpl.
    intros.
    etrans. cong. apply f_commutes.
    apply g_commutes.
  Qed.
  (** τ-proper **)
  Next Obligation.
    repeat intro.
    simpl.
    etrans. cong. apply H0. apply H.
  Qed.

  Infix "∘" := compose.

  Lemma left_id : ∀ T S (f : T ⇒ S), id ∘ f ≈ f.
  Proof.
    repeat intro; simpl. refl.
  Qed.

  Lemma right_id : ∀ T S (f : T ⇒ S), f ∘ id ≈ f.
  Proof.
    repeat intro; simpl. refl.
  Qed.

  Lemma compose_assoc T R S U (f : T ⇒ R) (g : R ⇒ S) (h : S ⇒ U) : h ∘ g ∘ f ≈ h ∘ (g ∘ f).
  Proof.
    repeat intro; simpl. refl.
  Qed.

  Canonical Structure 𝑺𝒕𝒓𝒆𝒂𝒎 : Category :=
    mkCategory left_id right_id compose_assoc.

End Defs.
