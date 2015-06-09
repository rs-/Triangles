Require Import Misc.Unicode.
Require Import Theory.Notations.
Require Import Category.Stream.Axioms.
Require Import Category.Stream.Terminality.

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＳＴＲＥＡＭ  ＭＯＤＥＬ  ＡＳ  Ａ  ＣＯＩＮＤＵＣＴＩＶＥ  ＴＹＰＥ
  ----------------------------------------------------------------------------*)
(** * Stream model as a coinductive type **)

Module StreamInstance : StreamAxioms.

  CoInductive Stream_ A : Type :=
    Cons : A → Stream_ A → Stream_ A.

  Arguments Cons {_} _ _.

  Notation "_∷_" := Cons.
  Notation "x ∷ xs" := (Cons x xs) (at level 60, right associativity).

  Definition Stream : Type → Type := Stream_.
  Definition head {A} : Stream A → A := λ s ∙ let '(x ∷ _) := s in x.
  Definition tail {A} : Stream A → Stream A := λ s ∙ let '(_ ∷ xs) := s in xs.

  CoFixpoint corec {A T} (hd : T → A) (tl : T → T) : T → Stream A :=
    λ t ∙ hd t ∷ corec hd tl (tl t).

  Lemma head_corec : ∀ {A T} {hd : T → A} {tl : T → T} {t}, head (corec hd tl t) = hd t.
  Proof.
    reflexivity.
  Qed.

  Lemma tail_corec : ∀ {A T} {hd : T → A} {tl : T → T} {t}, tail (corec hd tl t) = corec hd tl (tl t).
  Proof.
    reflexivity.
  Qed.

  (** Equivalence relation on streams **)
  Reserved Notation "x ∼ y" (at level 70, right associativity).

  CoInductive bisim_ {A} : Stream A → Stream A → Prop :=
  | bintro : ∀ {s₁ s₂ : Stream A}, head s₁ = head s₂ → tail s₁ ∼ tail s₂ → s₁ ∼ s₂
  where "s₁ ∼ s₂" := (@bisim_ _ s₁ s₂).

  Definition bisim {A} := @bisim_ A.

  Lemma bisim_head : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
  Proof.
    intros. now destruct H.
  Qed.
  Lemma bisim_tail : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
  Proof.
    intros. now destruct H.
  Qed.

  Lemma bisim_intro : ∀ {A}
                        (R : Stream A → Stream A → Prop)
                        (R_head : ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → head s₁ = head s₂)
                        (R_tail : ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → R (tail s₁) (tail s₂)),
                        ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → s₁ ∼ s₂.
  Proof.
    cofix Hc; constructor; intros.
    - now apply R_head.
    - eapply Hc; eauto.
  Qed.

End StreamInstance.

Module Terminality := StreamInstance <+ StreamTerminal.
