Require Import Category.Setoids.
Require Import Category.Sets.
Require Import Category.Sets_Setoids.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Category.Stream.
Require Import Theory.Category.
Require Import Theory.InitialTerminal.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.PrecompositionWithProduct.
Require Import Theory.PushforwardComodule.

Generalizable All Variables.


Module Type StreamAxioms.

  (** Stream and destructors **)
  Axiom Stream : 𝑺𝒆𝒕 → 𝑺𝒆𝒕.
  Axiom head : ∀ {A}, Stream A ⇒ A.
  Axiom tail : ∀ {A}, Stream A ⇒ Stream A.

  (** Equivalence relation on streams **)
  Axiom bisim : ∀ {A}, Stream A → Stream A → Prop.
  Infix "∼" := bisim (at level 70).

  Axiom bisim_head : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
  Axiom bisim_tail : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
  Notation "∼-head" := bisim_head (only parsing).
  Notation "∼-tail" := bisim_tail (only parsing).

  Declare Instance bisim_equiv : ∀ {A}, Equivalence (@bisim A).

  (** Redecoration of streams **)
  Axiom redec : ∀ {A B}, (Stream A ⇒ B) → Stream A ⇒ Stream B.
  Axiom head_redec : ∀ {A B} {f : Stream A ⇒ B}, head ∘ redec f ≈ f.
  Axiom tail_redec : ∀ {A B} {f : Stream A ⇒ B}, tail ∘ redec f ≈ redec f ∘ tail.
  Axiom redec_ext : ∀ {A B} {f g : Stream A ⇒ B}, f ≈ g → ∀ s, redec f s ∼ redec g s.
  Axiom redec_bisim : ∀ {A B} {f : Stream A ⇒ B} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → redec f s₁ ∼ redec f s₂.
  Axiom redec_head : ∀ {A} {s : Stream A}, redec head s ∼ s.
  Axiom redec_redec : ∀ {A B C} {f : Stream A ⇒ B} {g : Stream B ⇒ C} {s},
                        redec g (redec f s) ∼ redec (g ∘ redec f) s.

End StreamAxioms.

Module StreamTerminal (Import Ax : StreamAxioms).

  Lemma eq_bisim : ∀ {A} {s₁ s₂ : Stream A}, s₁ = s₂ → s₁ ∼ s₂.
  Proof.
    intros. now rewrite H.
  Qed.

  Lemma head_cong : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. now apply ∼-head.
  Qed.

  Lemma tail_cong : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. now apply ∼-tail.
  Qed.

  Program Definition STREAM (A : Type) : Setoids.Obj :=
    Setoids.make ⦃ Carrier ≔ Stream A ; Equiv ≔ bisim ⦄.

  Program Definition 𝒉𝒆𝒂𝒅 {A} : STREAM A ⇒ 𝑬𝑸 A := Setoids.Morphism.make head.
  Next Obligation.
    now apply head_cong.
  Qed.

  Program Definition 𝒕𝒂𝒊𝒍 {A} : STREAM A ⇒ STREAM A := Setoids.Morphism.make tail.
  Next Obligation.
    now apply tail_cong.
  Qed.

  Obligation Tactic := idtac.
  Program Definition 𝑺𝒕𝒓 : ‵ 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 𝑬𝑸 ′ :=
    RelativeComonad.make ⦃ T ≔ STREAM
                           ; counit ≔ λ X ∙ 𝒉𝒆𝒂𝒅
                           ; cobind ≔ λ X Y ∙ λ f ↦ Setoids.Morphism.make (redec f) ⦄.
  Next Obligation.
    intros. now apply redec_bisim.
  Qed.
  Next Obligation.
    intros X Y f g eq_fg x y eq_xy.
    etransitivity. eapply redec_bisim. apply eq_xy.
    apply redec_ext. intro. apply eq_fg. reflexivity.
  Qed.
  Next Obligation.
    intros A x y eq_xy. simpl.
    etransitivity. eapply redec_bisim. apply eq_xy.
    apply redec_head.
  Qed.
  Next Obligation.
    intros X Y f x y eq_xy. simpl.
    etransitivity. apply head_redec.
    now apply (Setoids.cong f).
  Qed.
  Next Obligation.
    intros X Y Z f g x y eq_xy. simpl.
    etransitivity. apply redec_redec.
    etransitivity. eapply redec_bisim. apply eq_xy. reflexivity.
  Qed.

  Program Definition 𝑻𝒂𝒊𝒍 : ‵ [𝑺𝒕𝒓] ⇒ [𝑺𝒕𝒓] ′ :=
    Comodule.make ⦃ α ≔ λ A ∙ Setoids.Morphism.make 𝒕𝒂𝒊𝒍 ⦄.
  Next Obligation.
    intros A x y eq_xy; now rewrite eq_xy.
  Qed.
  Next Obligation.
    intros C D f x y eq_xy. rewrite eq_xy.
    apply eq_bisim. apply tail_redec.
  Qed.

  Program Definition 𝑺𝑻𝑹 : ‵ 𝑺𝒕𝒓𝒆𝒂𝒎 ′ :=
    Stream.make ⦃ T ≔ 𝑺𝒕𝒓 ; tail ≔ 𝑻𝒂𝒊𝒍 ⦄.

End StreamTerminal.
