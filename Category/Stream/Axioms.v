Require Import Misc.Unicode.
Require Import Theory.Notations.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＡＸＩＯＭＳ  ＦＯＲ  ＳＴＲＥＡＭＳ
  ----------------------------------------------------------------------------*)
(** * Axioms for streams **)

Module Type StreamAxioms.

  (** ** Stream type and destructors **)
  Axiom Stream : Type → Type.
  Axiom head : ∀ {A}, Stream A → A.
  Axiom tail : ∀ {A}, Stream A → Stream A.

  (** ** Corecursor on Stream and computation rules **)
  Axiom corec : ∀ {A T}, (T → A) → (T → T) → T → Stream A.
  Axiom head_corec : ∀ {A T} {hd : T → A} {tl : T → T} {t}, head (corec hd tl t) = hd t.
  Axiom tail_corec : ∀ {A T} {hd : T → A} {tl : T → T} {t}, tail (corec hd tl t) = corec hd tl (tl t).

  (** ** Equivalence relation on streams **)
  Axiom bisim : ∀ {A}, Stream A → Stream A → Prop.
  Infix "∼" := bisim (at level 70).

  (** ** Bisimulation elimination rules **)
  Axiom bisim_head : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
  Axiom bisim_tail : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
  Notation "∼-head" := bisim_head (only parsing).
  Notation "∼-tail" := bisim_tail (only parsing).

  (** ** Coinduction principle **)
  Axiom bisim_intro : ∀ {A}
                        (R : Stream A → Stream A → Prop)
                        (R_head : ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → head s₁ = head s₂)
                        (R_tail : ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → R (tail s₁) (tail s₂)),
                        ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → s₁ ∼ s₂.

End StreamAxioms.
