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

(*------------------------------------------------------------------------------
  -- ＳＴＲＥＡＭ  ＩＳ  Ａ  ＴＥＲＭＩＮＡＬ  ＯＢＪＥＣＴ
  ----------------------------------------------------------------------------*)

CoInductive Stream (A : Type) : Type :=
  Cons : A → Stream A → Stream A.

Arguments Cons {_} _ _.

Notation "_∷_" := Cons.
Notation "x ∷ xs" := (Cons x xs) (at level 60, right associativity).

(** Destructors **)
Definition head {A} (s : Stream A) : A         := let '(x ∷ _)   := s in x.
Definition tail {A} (s : Stream A) : Stream A  := let '(_ ∷ xs)  := s in xs.

(** Bisimulation **)
Reserved Notation "x ∼ y" (at level 70, right associativity).

CoInductive bisim {A} : Stream A → Stream A → Prop :=
| bintro : ∀ {s₁ s₂ : Stream A}, head s₁ = head s₂ → tail s₁ ∼ tail s₂ → s₁ ∼ s₂
where "s₁ ∼ s₂" := (@bisim _ s₁ s₂).

Notation "_∼_" := bisim.

Lemma head_cong : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
Proof.
  intros A s₁ s₂ eq_s₁s₂. now destruct eq_s₁s₂.
Qed.

Lemma tail_cong : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
Proof.
  intros A s₁ s₂ eq_s₁s₂. now destruct eq_s₁s₂.
Qed.

Program Definition STREAM (A : Type) : Setoids.Obj :=
  Setoids.make ⦃ Carrier ≔ Stream A ; Equiv ≔ bisim ⦄.
Next Obligation.
  constructor.
  - cofix Hc; constructor; intros.
    + reflexivity.
    + now apply Hc.
  - cofix Hc; constructor; intros.
    + symmetry; now apply head_cong.
    + apply Hc; now apply tail_cong.
  - cofix Hc; constructor; intros.
    + destruct H. destruct H0. etransitivity; eauto.
    + eapply Hc; eapply tail_cong; eauto.
Qed.

Instance bisim_equiv : ∀ {A}, Equivalence (@bisim A).
Proof.
  intros. apply (Setoids.is_SEquiv (STREAM A)).
Qed.

Program Definition 𝒉𝒆𝒂𝒅 {A} : STREAM A ⇒ 𝑬𝑸 A := Setoids.Morphism.make head.
Next Obligation.
  now apply head_cong.
Qed.

Program Definition 𝒕𝒂𝒊𝒍 {A} : STREAM A ⇒ STREAM A := Setoids.Morphism.make tail.
Next Obligation.
  now apply tail_cong.
Qed.

CoFixpoint redec {A B} (f : Stream A → B) (s : Stream A) : Stream B :=
  f s ∷ redec f (𝒕𝒂𝒊𝒍 s).

Obligation Tactic := idtac.
Program Definition 𝑺𝒕𝒓 : ‵ 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 𝑬𝑸 ′ :=
  RelativeComonad.make ⦃ T ≔ STREAM
                       ; counit ≔ λ X ∙ 𝒉𝒆𝒂𝒅
                       ; cobind ≔ λ X Y ∙ λ f ↦ Setoids.Morphism.make (redec f) ⦄.
Next Obligation.
  cofix Hc; constructor.
  - simpl. now rewrite H.
  - apply Hc. now rewrite H.
Qed.
Next Obligation.
  cofix Hc; constructor; intros.
  - simpl. rewrite H0. now apply H.
  - apply Hc; auto. now rewrite H0.
Qed.
Next Obligation.
  cofix Hc; constructor; intros.
  - simpl. now apply head_cong.
  - apply Hc. rewrite H. reflexivity.
Qed.
Next Obligation.
  repeat intro. now rewrite H.
Qed.
Next Obligation.
  cofix Hc; constructor; intros.
  - apply (Setoids.cong g). rewrite H. reflexivity.
  - apply Hc. now rewrite H.
Qed.

Program Definition 𝑻𝒂𝒊𝒍 : ‵ [𝑺𝒕𝒓] ⇒ [𝑺𝒕𝒓] ′ :=
  Comodule.make ⦃ α ≔ λ A ∙ Setoids.Morphism.make 𝒕𝒂𝒊𝒍 ⦄.
Next Obligation.
  intros A x y eq_xy; now rewrite eq_xy.
Qed.
Next Obligation.
  intros C D f x y eq_xy. now rewrite eq_xy.
Qed.

Program Definition 𝑺𝑻𝑹 : ‵ 𝑺𝒕𝒓𝒆𝒂𝒎 ′ :=
  Stream.make ⦃ T ≔ 𝑺𝒕𝒓 ; tail ≔ 𝑻𝒂𝒊𝒍 ⦄.

Section Defs.

  Variable (Tr : 𝑺𝒕𝒓𝒆𝒂𝒎).

  Notation T                  := (Stream.T Tr).
  Notation "'T⋅tail'"         := (Stream.tail Tr _).
  Notation "'T⋅tail[' A ]"    := (Stream.tail Tr A) (only parsing).
  Notation STR                := (Stream.T 𝑺𝑻𝑹).
  Notation "'STR⋅tail'"       := (Stream.tail 𝑺𝑻𝑹 _).
  Notation "'STR⋅tail[' A ]"  := (Stream.tail 𝑺𝑻𝑹 A) (only parsing).

  Local Notation "a ∼ b" := (SEquiv a b).

  CoFixpoint tau {A} (t : T A) : STR A :=
    T⋅counit t ∷ tau (T⋅tail t).

  Lemma head_tau : ∀ A (t : T A), STR⋅counit (tau t) = T⋅counit t.
  Proof.
    reflexivity.
  Qed.

  Lemma tail_tau : ∀ A (t : T A), STR⋅tail (tau t) = tau (T⋅tail t).
  Proof.
    reflexivity.
  Qed.

  Lemma tau_cong : ∀ A (x y : T A), x ∼ y → tau x ∼ tau y.
  Proof.
    cofix Hc; intros A x y eq_xy. constructor.
    - simpl. now rewrite eq_xy.
    - simpl. apply Hc. now rewrite eq_xy.
  Qed.

  Program Definition Tau {A} : T A ⇒ STR A :=
    Setoids.Morphism.make tau.
  Next Obligation.
    intros. now apply tau_cong.
  Qed.

  Lemma tau_counit : ∀ A (t t' : T A), t ∼ t' → T⋅counit t ∼ STR⋅counit (tau t').
  Proof.
    intros A t t' eq_tt'. now rewrite eq_tt'.
  Qed.

  Lemma tau_cobind_trans :
    ∀ A B (f : STR A ⇒ 𝑬𝑸 B) x t₁ t₂,
      t₁ ∼ Tau (T⋅cobind (f ∘ Tau) x) → STR⋅cobind f (Tau x) ∼ t₂ → t₁ ∼ t₂.
  Proof.
    cofix Hc; intros A B f x t₁ t₂ eq_t₁ eq_t₂; constructor.
    - change (𝒉𝒆𝒂𝒅 t₁ = 𝒉𝒆𝒂𝒅 t₂); rewrite eq_t₁, <- eq_t₂; clear eq_t₁ eq_t₂.
      etransitivity; [ apply head_tau |].
      etransitivity; [ apply (counit_cobind T); reflexivity |].
      reflexivity.
    - apply Hc with (f := f) (x := T⋅tail x);
      [ change (tail t₁) with (𝒕𝒂𝒊𝒍 t₁); rewrite eq_t₁
      | change (tail t₂) with (𝒕𝒂𝒊𝒍 t₂); rewrite <- eq_t₂]; clear eq_t₁ eq_t₂.
      + apply tau_cong. etransitivity.  apply (α_commutes (Stream.tail Tr)); reflexivity.
        apply (Π.cong _ _ (T⋅cobind)); [| reflexivity ].
        intros u v eq_uv. simpl.
        apply (Setoids.cong f). now apply tau_cong.
      + reflexivity.
  Qed.

  Lemma tau_cobind : ∀ A B (f : STR A ⇒ 𝑬𝑸 B) x y, x ∼ y → Tau (T⋅cobind (f ∘ Tau) x) ∼ STR⋅cobind f (Tau y).
  Proof.
    intros A B f x y eq_xy. rewrite eq_xy.
    apply tau_cobind_trans with (f := f) (x := y); reflexivity.
  Qed.

End Defs.

(** printing τ #◯# *)

(** ◯ is a morphism of triangles **)
Program Definition τ (T : 𝑺𝒕𝒓𝒆𝒂𝒎) : T ⇒ 𝑺𝑻𝑹 :=
  Stream.make ⦃ τ ≔ RelativeComonad.make ⦃ τ ≔ λ A ∙ Tau T ⦄ ⦄.
(** τ-counit **)
Next Obligation.
  repeat intro. now apply tau_counit.
Qed.
(** τ-cobind **)
Next Obligation.
  repeat intro. now apply tau_cobind.
Qed.
(** τ-commutes **)
Next Obligation.
  repeat intro. apply tau_cong. now rewrite H.
Qed.

(* begin hide *)
Local Notation "⟨ f ⟩" := (RelativeComonad.τ (m := Stream.τ f)) (only parsing).
(* end hide *)

(** 𝑺𝑻𝑹 is a terminal object **)
Program Definition Coinitiality : Terminal 𝑺𝒕𝒓𝒆𝒂𝒎 :=
  Terminal.make  ⦃ one  ≔ 𝑺𝑻𝑹
                 ; top  ≔ τ ⦄.
Next Obligation.
  cut (∀ (T : 𝑺𝒕𝒓𝒆𝒂𝒎) (f g : T ⇒ 𝑺𝑻𝑹) (A : 𝑺𝒆𝒕) (t : Stream.T T A) t₁ t₂,
         t₁ ∼ ⟨f⟩ A t → ⟨g⟩ A t ∼ t₂ → t₁ ∼ t₂); [repeat intro |].
  - rewrite H0. apply H with (f := f) (g := τ _) (t := y); reflexivity.
  - cofix Hc; intros T f g A t t₁ t₂ eq_t₁ eq_t₂; constructor.
    + change (𝒉𝒆𝒂𝒅 t₁ = 𝒉𝒆𝒂𝒅 t₂); rewrite eq_t₁, <- eq_t₂; clear eq_t₁ eq_t₂.
      etransitivity. symmetry. apply (τ_counit (Stream.τ f)); reflexivity.
      symmetry.
      etransitivity. symmetry. apply (τ_counit (Stream.τ g)); reflexivity.
      reflexivity.
    + change (𝒕𝒂𝒊𝒍 t₁ ∼ 𝒕𝒂𝒊𝒍 t₂); eapply Hc; [ rewrite eq_t₁ | rewrite <- eq_t₂ ]; clear eq_t₁ eq_t₂.
      * symmetry. eapply (Stream.τ_commutes f); reflexivity.
      * eapply (Stream.τ_commutes g); reflexivity.
Qed.