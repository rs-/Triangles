Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.RelativeComonadWithCut.
Require Import Category.RComod.
Require Import Category.Setoids.
Require Import Category.Sets.
Require Import Category.Sets_Setoids.
Require Import Category.RComonad.
Require Import InfiniteTriangles.redecInfiniteTriangles8_4.
Require Import Category.Coinitiality.
Require Import Theory.Comodule.
Require Import Theory.PrecompositionWithProduct.
Require Import Theory.PushforwardComodule.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＩＮＦＩＮＩＴＥ  ＴＲＥＥＳ
  ----------------------------------------------------------------------------*)
(** * Infinite trees over a signature **)

CoInductive ITree P S :=
  node : S → (P → ITree P S) → ITree P S.

Arguments node {_ _} _ _.

Definition head {P S} (t : ITree P S) : S := let '(node σ _) := t in σ.
Definition tail {P S} (t : ITree P S) : P → ITree P S := let '(node _ ts) := t in ts.
Definition tail' {P S} (p : P) (t : ITree P S) : ITree P S := tail t p.

Reserved Notation "a ∼ b" (at level 70, right associativity).

CoInductive bisim {P S} : ITree P S → ITree P S → Prop :=
  bnode : ∀ {t₁ t₂ : ITree P S}, head t₁ = head t₂ → (∀ p, tail t₁ p ∼ tail t₂ p) → t₁ ∼ t₂
where "a ∼ b" := (@bisim _ _ a b).

Notation "_∼_" := bisim (only parsing).

Instance bisim_equiv {P S} : Equivalence (@bisim P S).
Proof.
  constructor.
  - cofix bisim.
    constructor.
    + reflexivity.
    + intros p. apply bisim.
  - cofix bisim.
    intros t₁ t₂ eq_t₁t₂.
    constructor.
    + now destruct eq_t₁t₂.
    + intros p. apply bisim. now destruct eq_t₁t₂.
  - cofix bisim.
    intros t₁ t₂ t₃ eq_t₁t₂ eq_t₂t₃.
    constructor.
    + destruct eq_t₁t₂ , eq_t₂t₃; congruence.
    + intro p. eapply bisim; [destruct eq_t₁t₂ | destruct eq_t₂t₃]; auto.
Qed.

Lemma head_cong : ∀ {P S} {t₁ t₂ : ITree P S}, t₁ ∼ t₂ → head t₁ = head t₂.
Proof.
  intros. now destruct H.
Qed.

Lemma tail_cong : ∀ {P S} {p} {t₁ t₂ : ITree P S}, t₁ ∼ t₂ → tail t₁ p ∼ tail t₂ p.
Proof.
  intros. now destruct H.
Qed.

CoFixpoint redec {P} {A B} (f : ITree P A → B) (t : ITree P A) : ITree P B :=
  node (f t) (λ p ∙ redec f (tail t p)).

Lemma head_redec : ∀ {P} {A B} (f : ITree P A → B) t, head (redec f t) = f t.
Proof.
  reflexivity.
Qed.

Lemma tail_redec : ∀ {P} {A B} (f : ITree P A → B) t p, tail (redec f t) p = redec f (tail t p).
Proof.
  reflexivity.
Qed.

Definition fcompat {P} {A B} (f : ITree P A → B) := ∀ t₁ t₂, t₁ ∼ t₂ → f t₁ = f t₂.

Lemma redec_cong : ∀ {P} {A B} {f : ITree P A → B} (fcong : fcompat f) {t₁ t₂}, t₁ ∼ t₂ → redec f t₁ ∼ redec f t₂.
Proof.
  cofix bisim; intros.
  constructor.
  - now apply fcong.
  - intro p. apply bisim; auto. now destruct H.
Qed.

Notation "'S-redec_cong'" := redec_cong.

Lemma redec_ext : ∀ {P} {A B} {f g : ITree P A → B}, (∀ x, f x = g x) → ∀ t, redec f t ∼ redec g t.
Proof.
  cofix bisim; intros.
  constructor.
  - apply H.
  - intro p. apply bisim; auto.
Qed.

Hint Extern 1 (fcompat (Setoids.map ?f)) => (repeat intro; now apply (Setoids.cong f)).

Program Definition 𝑰𝑻𝒓𝒆𝒆 P : RelativeComonad 𝑬𝑸 :=
  RelativeComonad.make ⦃ T       ≔ λ S ∙ Setoids.make ⦃ Carrier ≔ ITree P S ; Equiv ≔ bisim ⦄
                       ; counit  ≔ λ A ∙ Setoids.Morphism.make head
                       ; cobind  ≔ λ A B ∙ λ f ↦ Setoids.Morphism.make (redec f) ⦄.
(** _∼_ equiv **)
Next Obligation.
  eauto with typeclass_instances.
Qed.
(** counit-cong **)
Next Obligation.
  now destruct H.
Qed.
(** cobind-cong **)
Next Obligation.
  apply redec_cong; auto.
Qed.
(** cobind-cong₂ **)
Next Obligation.
  intros f g eq_fg t₁ t₂ eq_t₁t₂. etransitivity.
  - apply redec_cong; auto. exact eq_t₁t₂.
  - apply redec_ext. intro x; apply eq_fg; reflexivity.
Qed.
(** cobind-counit **)
Next Obligation.
  revert x y H. cofix bisim. intros t₁ t₂ eq_t₁t₂.
  constructor.
  - now destruct eq_t₁t₂.
  - intro p. apply bisim. now destruct eq_t₁t₂.
Qed.
(** counit-cobind **)
Next Obligation.
  now apply (Setoids.cong f).
Qed.
(** cobind-cobind **)
Next Obligation.
  revert x y H. cofix bisim. intros t₁ t₂ eq_t₁t₂.
  constructor.
  - apply (Setoids.cong g).
    apply redec_cong; auto.
  - intro p. apply bisim. now destruct eq_t₁t₂.
Qed.

(** Streams **)
Definition Stream := ITree unit.
Definition 𝑺𝒕𝒓𝒆𝒂𝒎 := 𝑰𝑻𝒓𝒆𝒆 unit.
Notation "'S-redec'" := redec.

Definition cut {E A} (t : 𝑺𝒕𝒓𝒆𝒂𝒎 (E ⟨×⟩ A)) : 𝑺𝒕𝒓𝒆𝒂𝒎 A := lift 𝑺𝒕𝒓𝒆𝒂𝒎 snd t.
Notation "'S-cut'" := cut.

Lemma head_cut : ∀ {E A} (t : Stream (E ⟨×⟩ A)), head (cut t) = snd (head t).
Proof.
  reflexivity.
Qed.

Lemma tail_cut : ∀ {E A} (t : Stream (E ⟨×⟩ A)) p, tail (cut t) p = cut (tail t p).
Proof.
  reflexivity.
Qed.

Notation "x ∷ xs" := (node x (λ _ ∙ xs)) (at level 70, right associativity).

Definition add {A E} (e : E) (s : Stream A) : Stream (E ⟨×⟩ A) :=
  lift 𝑺𝒕𝒓𝒆𝒂𝒎 (λ a ∙ (e , a)) s.

Program Definition 𝑨𝒅𝒅 {E : 𝑺𝒆𝒕} (e : E) : ‵ [𝑺𝒕𝒓𝒆𝒂𝒎] ⇒ [↑[𝑺𝒕𝒓𝒆𝒂𝒎]][E×─] ′ :=
  Comodule.make ⦃ α ≔ λ A ∙ Setoids.Morphism.make (add e) ⦄.
Next Obligation.
  revert x y H. cofix Hc; intros.
  constructor.
  - simpl. f_equal. now apply head_cong.
  - intro p. apply Hc. now apply tail_cong.
Qed.
Next Obligation.
  assert (∀ {E A} (e : E) (t : Stream A), cut (add e t) ∼ t). {
    cofix Hc; intros.
    constructor.
    - simpl. reflexivity.
    - intro p. apply Hc.
  }

  revert x y H; cofix Hc; intros.
  constructor.
  - rewrite head_redec. simpl. f_equal. apply (Setoids.cong f).
    etransitivity. apply H. symmetry. apply H0.
  - intro p. apply Hc. now apply tail_cong.
Qed.