Require Import Misc.Unicode.
Require Import Theory.Notations.
Require Import Category.TriMat.Axioms.
Require Import Category.TriMat.Terminality.

(*------------------------------------------------------------------------------
  -- ＴＲＩ  ＭＯＤＥＬ  ＡＳ  Ａ  ＣＯＩＮＤＵＣＴＩＶＥ  ＴＹＰＥ
  ----------------------------------------------------------------------------*)
(** * Tri model as a coinductive type **)

Module TriInstance (Import TE : Typ) <: TriMatAxioms TE.

  Local Notation E := TE.t (only parsing).

  CoInductive Tri_ A : Type :=
    constr : A → Tri_ (E ⟨×⟩ A) → Tri_ A.

  Definition Tri : Type → Type := Tri_.
  Definition top : ∀ {A}, Tri A → A := λ _ t ∙ let '(constr x _) := t in x.
  Definition rest : ∀ {A}, Tri A → Tri (E ⟨×⟩ A) := λ _ t ∙ let '(constr _ t') := t in t'.

  (** Corecursor on Tri **)
  Definition corec {T : Type → Type} (tp : ∀ A, T A → A) (rt : ∀ A, T A → T (E ⟨×⟩ A)) : ∀ {A}, T A → Tri A :=
    let cofix corec {A} (t : T A) : Tri A :=
        constr _ (tp _ t) (corec (rt _ t))
    in @corec.

  Lemma top_corec : ∀ {A} {T : Type → Type}
                       {hd : ∀ A, T A → A} {tl : ∀ A, T A → T (E ⟨×⟩ A)} {t : T A},
                       top (corec hd tl t) = hd A t.
  Proof.
    reflexivity.
  Qed.
  Lemma rest_corec : ∀ {A} {T : Type → Type}
                       {hd : ∀ A, T A → A} {tl : ∀ A, T A → T (E ⟨×⟩ A)} {t : T A},
                       rest (corec hd tl t) = corec hd tl (tl A t).
  Proof.
    reflexivity.
  Qed.

  (** Equivalence relation on streams **)
  CoInductive bisim_ : ∀ {A}, Tri A → Tri A → Prop :=
    bisim_constr : ∀ {A} {t₁ t₂ : Tri A}, top t₁ = top t₂ → bisim_ (rest t₁) (rest t₂) → bisim_ t₁ t₂.

  Definition bisim : ∀ {A}, Tri A → Tri A → Prop := @bisim_.
  Infix "∼" := bisim (at level 70).

  Lemma bisim_top : ∀ {A} {s₁ s₂ : Tri A}, s₁ ∼ s₂ → top s₁ = top s₂.
  Proof.
    intros. now destruct H.
  Qed.
  Lemma bisim_rest : ∀ {A} {s₁ s₂ : Tri A}, s₁ ∼ s₂ → rest s₁ ∼ rest s₂.
  Proof.
    intros. now destruct H.
  Qed.
  Notation "∼-top" := bisim_top (only parsing).
  Notation "∼-rest" := bisim_rest (only parsing).

  Lemma bisim_intro : ∀ (R : ∀ {X}, Tri X → Tri X → Prop)
                        (R_top : ∀ {A} {s₁ s₂ : Tri A}, R s₁ s₂ → top s₁ = top s₂)
                        (R_rest : ∀ {A} {s₁ s₂ : Tri A}, R s₁ s₂ → R (rest s₁) (rest s₂)),
                        ∀ {A} {s₁ s₂ : Tri A}, R s₁ s₂ → s₁ ∼ s₂.
  Proof.
    cofix Hc; constructor; intros.
    - now apply R_top.
    - eapply Hc; eauto. now apply R_rest.
  Qed.


End TriInstance.


Module Terminality (TE : Typ) := TE <+ TriInstance <+ TriMatTerminal.