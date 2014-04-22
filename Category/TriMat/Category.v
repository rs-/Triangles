(*

   Benedikt Ahrens and Régis Spadotti

   Coinitial semantics for redecoration of triangular matrices

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of the category of coalgebras for the signature of infinite tri. matrices

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
(** * Category of triangular matrices **)

(** ** Object and morphism definitions **)
Module TriMat.

  Structure Obj (E : 𝑻𝒚𝒑𝒆) : Type := mkObj
  { T         :>  𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝒕 𝑬𝑸 E
  ; rest      :>  [T] ⇒ [T][E×─]
  ; rest_cut  :   ∀ {A}, rest(A) ∘ T⋅cut ≈ T⋅cut ∘ rest(E × A) }.

  Arguments mkObj     {_ _ _} _.
  Arguments T         {_} _.
  Arguments rest      {_} _.
  Arguments rest_cut  {_} _ {_ _ _ _}.

  Notation "'TriMat.make' ⦃ 'T' ≔ T ; 'rest' ≔ rest ⦄" :=
           (@mkObj _ T rest _) (only parsing).

  Structure Morphism {E} (T S : Obj E) : Type := mkMorphism
  { τ           :> T ⇒ S
  ; τ_commutes  : ⟨τ⟩［E×─］ ∘ Φ ∘ τ⁎⋅T ≈ S ∘ ⟨τ⟩ }.

  Arguments mkMorphism  {_ _ _ _} _.
  Arguments τ           {_ _ _} _.
  Arguments τ_commutes  {_ _ _} _ {_ _ _ _}.

  Notation "'TriMat.make' ⦃ 'τ' ≔ τ ⦄" := (@mkMorphism _ _ _ τ _) (only parsing).

  Program Definition Hom {E} (T S : Obj E) : Setoid :=
    Setoid.make   ⦃ Carrier  ≔ Morphism T S
                  ; Equiv    ≔ (λ g f ∙ g ≈ f) ⦄.
  (** equivalence **)
  Next Obligation.
    constructor.
    - repeat intro. now rewrite H.
    - repeat intro. symmetry; now rewrite H.
    - repeat intro; etransitivity; eauto. now apply H0.
  Qed.

End TriMat.

Export TriMat.

(** ** Identity and compositon definitions **)

Section Defs.


  Variable (E : 𝑻𝒚𝒑𝒆).

  Implicit Types (T S R U : Obj E).

  Infix "⇒" := Hom.

  Program Definition id {T} : T ⇒ T :=
    TriMat.make ⦃ τ ≔ id[T] ⦄.
  (** τ-cong **)
  Next Obligation.
    now rewrite H.
  Qed.

  Obligation Tactic := idtac.
  Program Definition compose {T S R} : [ S ⇒ R ⟶ T ⇒ S ⟶ T ⇒ R ] :=
    λ g f ↦₂ TriMat.make ⦃ τ ≔ g ∘ f ⦄.
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
  (** τ-cong **)
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
