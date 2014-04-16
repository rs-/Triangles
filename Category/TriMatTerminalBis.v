Require Import InfiniteTriangles.redecInfiniteTriangles8_4.
Require Import Category.Setoids.
Require Import Category.Sets.
Require Import Category.Sets_Setoids.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Category.RComonadWithCut.
Require Import Category.TriMat.
Require Import Theory.Category.
Require Import Theory.InitialTerminal.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.PrecompositionWithProduct.
Require Import Theory.PushforwardComodule.

Generalizable All Variables.


Module Type TriMatAxioms (Import TE : Elt).

  (** Stream and destructors **)
  Axiom Tri : Type → Type.
  Axiom top : ∀ {A}, Tri A → A.
  Axiom rest : ∀ {A}, Tri A → Tri (E ⟨×⟩ A).

  (** Corecursor on Tri **)
  Axiom corec : ∀ {T : Type → Type}, (∀ A, T A → A) → (∀ A, T A → T (E ⟨×⟩ A)) → ∀ {A}, T A → Tri A.
  Axiom head_corec : ∀ {A} {T : Type → Type}
                       {hd : ∀ A, T A → A} {tl : ∀ A, T A → T (E ⟨×⟩ A)} {t : T A},
                       top (corec hd tl t) = hd A t.
  Axiom tail_corec : ∀ {A} {T : Type → Type}
                       {hd : ∀ A, T A → A} {tl : ∀ A, T A → T (E ⟨×⟩ A)} {t : T A},
                       rest (corec hd tl t) = corec hd tl (tl A t).

  (** Equivalence relation on streams **)
  Axiom bisim : ∀ {A}, Tri A → Tri A → Prop.
  Infix "∼" := bisim (at level 70).

  Axiom bisim_head : ∀ {A} {s₁ s₂ : Tri A}, s₁ ∼ s₂ → top s₁ = top s₂.
  Axiom bisim_tail : ∀ {A} {s₁ s₂ : Tri A}, s₁ ∼ s₂ → rest s₁ ∼ rest s₂.
  Notation "∼-head" := bisim_head (only parsing).
  Notation "∼-tail" := bisim_tail (only parsing).

  Axiom bisim_intro : ∀ (R : ∀ {X}, Tri X → Tri X → Prop)
                        (R_top : ∀ {A} {s₁ s₂ : Tri A}, R s₁ s₂ → top s₁ = top s₂)
                        (R_rest : ∀ {A} {s₁ s₂ : Tri A}, R s₁ s₂ → R (rest s₁) (rest s₂)),
                        ∀ {A} {s₁ s₂ : Tri A}, R s₁ s₂ → s₁ ∼ s₂.

End TriMatAxioms.

Module TriMatTerminal (Import TE : Elt) (Import Ax : TriMatAxioms TE).

  Notation coRec hd tl := (corec (λ _ ∙ hd) (λ _ ∙ tl)) (only parsing).

  Definition cut {A} : Tri (E ⟨×⟩ A) → Tri A := coRec (λ x ∙ snd (top x)) rest.

  Definition lift {A B : Type} (f : Tri A → B) : Tri (E ⟨×⟩ A) → E ⟨×⟩ B := λ x ∙ (fst (top x) , f (cut x)).

  Definition redec' : ∀ {B : Type}, { A : Type & Tri A → B & Tri A} → Tri B.
  Proof.
    apply (@corec (λ B ∙ { A : Type & Tri A → B & Tri A })).
    - intros B [A f t].
      exact (f t).
    - intros B [A f t].
      exists (E ⟨×⟩ A).
      + exact (lift f).
      + exact (rest t).
  Defined.

  Definition redec {A B : Type} (f : Tri A → B) (t : Tri A) : Tri B :=
    @redec' B (existT2 (λ A ∙ Tri A → B) (λ A ∙ Tri A) A f t).

  Lemma top_redec : ∀ {A B} (f : Tri A → B) (t : Tri A), top (redec f t) = f t.
  Proof.
    intros. unfold redec, redec'. generalize (@head_corec); intros.
    specialize (H B). specialize (H (λ B ∙ { A : Type & Tri A → B & Tri A })).
    specialize (H (λ A X ∙ let (u, v, w) := X in v w)).
    specialize (H (λ A X ∙ let (u, v, w) := X in existT2 _ _ (E ⟨×⟩ u) (lift v) (rest w))).
    specialize (H (existT2 (λ A ∙ Tri A → B) (λ A ∙ Tri A) A f t)).
    simpl in *.
    symmetry. etransitivity. symmetry. apply H. reflexivity.
  Qed.

  Lemma rest_redec : ∀ {A B} (f : Tri A → B) (t : Tri A), rest (redec f t) = redec (lift f) (rest t).
  Proof.
    intros. unfold redec, redec'.
    generalize (@tail_corec); intros.
    specialize (H B). specialize (H (λ B ∙ { A : Type & Tri A → B & Tri A })).
    specialize (H (λ A X ∙ let (u, v, w) := X in v w)).
    specialize (H (λ A X ∙ let (u, v, w) := X in existT2 _ _ (E ⟨×⟩ u) (lift v) (rest w))).
    specialize (H (existT2 (λ A ∙ Tri A → B) (λ A ∙ Tri A) A f t)).
    simpl in *. etransitivity. apply H. reflexivity.
  Qed.

End TriMatTerminal.
