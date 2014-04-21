Require Export Structures.Equalities.
Require Import Misc.Unicode.
Require Import Theory.Notations.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＡＸＩＯＭＳ  ＦＯＲ  ＴＲＩＡＮＧＵＬＡＲ  ＭＡＴＲＩＣＥＳ
  ----------------------------------------------------------------------------*)
(** * Axioms for triangular matrices **)

Module Type TriMatAxioms (Import TE : Typ).

  Local Notation E := TE.t (only parsing).

  (** Tri type and destructors **)
  Axiom Tri : Type → Type.
  Axiom top : ∀ {A}, Tri A → A.
  Axiom rest : ∀ {A}, Tri A → Tri (E ⟨×⟩ A).

  (** Corecursor on Tri and computation rules**)
  Axiom corec : ∀ {T : Type → Type}, (∀ A, T A → A) → (∀ A, T A → T (E ⟨×⟩ A)) → ∀ {A}, T A → Tri A.
  Axiom top_corec : ∀ {A} {T : Type → Type}
                       {hd : ∀ A, T A → A} {tl : ∀ A, T A → T (E ⟨×⟩ A)} {t : T A},
                       top (corec hd tl t) = hd A t.
  Axiom rest_corec : ∀ {A} {T : Type → Type}
                       {hd : ∀ A, T A → A} {tl : ∀ A, T A → T (E ⟨×⟩ A)} {t : T A},
                       rest (corec hd tl t) = corec hd tl (tl A t).

  (** Equivalence relation on triangular matrices **)
  Axiom bisim : ∀ {A}, Tri A → Tri A → Prop.
  Infix "∼" := bisim (at level 70).

  (** bisim destructors **)
  Axiom bisim_top : ∀ {A} {s₁ s₂ : Tri A}, s₁ ∼ s₂ → top s₁ = top s₂.
  Axiom bisim_rest : ∀ {A} {s₁ s₂ : Tri A}, s₁ ∼ s₂ → rest s₁ ∼ rest s₂.
  Notation "∼-top" := bisim_top (only parsing).
  Notation "∼-rest" := bisim_rest (only parsing).

  (** Coinduction principle **)
  Axiom bisim_intro : ∀ (R : ∀ {X}, Tri X → Tri X → Prop)
                        (R_top : ∀ {A} {s₁ s₂ : Tri A}, R s₁ s₂ → top s₁ = top s₂)
                        (R_rest : ∀ {A} {s₁ s₂ : Tri A}, R s₁ s₂ → R (rest s₁) (rest s₂)),
                        ∀ {A} {s₁ s₂ : Tri A}, R s₁ s₂ → s₁ ∼ s₂.

End TriMatAxioms.