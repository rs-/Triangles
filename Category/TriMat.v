(**

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

Require Import Category.Types.
Require Import Category.Setoids.
Require Import Category.Types_Setoids.
Require Import Category.RComod.
Require Import Category.RComonadWithCut.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.PrecompositionWithProduct.
Require Import Theory.PushforwardComodule.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＯＦ  ＴＲＩＡＮＧＬＥＳ
  ----------------------------------------------------------------------------*)

Module TriMat.

  Structure Obj (E : 𝑻𝒚𝒑𝒆) : Type := mkObj
  { T        :> 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝒕 𝑬𝑸 E
  ; α        :> [T] ⇒ [T][E×─]
  ; α_cut    : ∀ {A}, α(A) ∘ T⋅cut ≈ T⋅cut ∘ α(E × A) }.

  Arguments mkObj {_ _ _} _.
  Arguments T     {_} _.
  Arguments α     {_} _.
  Arguments α_cut {_} _ {_ _ _ _}.

  Notation make T α := (@mkObj _ T α _) (only parsing).

  Structure Morphism {E} (T S : Obj E) : Type := mkMorphism
  { τ :> T ⇒ S
  ; τ_commutes : ⟨τ⟩［E×─］ ∘ Φ ∘ τ⁎⋅T ≈ S ∘ ⟨τ⟩ }.

  Arguments mkMorphism {_ _ _ _} _.
  Arguments τ          {_ _ _} _.
  Arguments τ_commutes {_ _ _} _ {_ _ _ _}.

  Module Morphism.

    Notation make τ := (@mkMorphism _ _ _ τ _) (only parsing).

  End Morphism.

  Program Definition Hom {E} (T S : Obj E) : Setoid :=
    Setoid.make (Morphism T S) (λ g f ∙ g ≈ f).
  Next Obligation.
    constructor.
    - repeat intro. now rewrite H.
    - repeat intro. symmetry; now rewrite H.
    - repeat intro; etransitivity; eauto. now apply H0.
  Qed.

End TriMat.

Export TriMat.

Section Defs.


  Variable (E : 𝑻𝒚𝒑𝒆).

  Implicit Types (T S R U : Obj E).

  Infix "⇒" := Hom.

  Program Definition id {T} : T ⇒ T :=
    TriMat.Morphism.make (id[T]).
  Next Obligation.
    now rewrite H.
  Qed.

  Obligation Tactic := idtac.
  Program Definition compose {T S R} : [ S ⇒ R ⟶ T ⇒ S ⟶ T ⇒ R ] :=
    λ g f ↦₂ TriMat.Morphism.make (g ∘ f).
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

  Canonical Structure 𝑻𝒓𝒊𝑴𝒂𝒕 : Category :=
    mkCategory left_id right_id compose_assoc.

End Defs.
