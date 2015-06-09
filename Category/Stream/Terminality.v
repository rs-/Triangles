Require Import Category.Setoids.
Require Import Category.Types.
Require Import Category.Types_Setoids.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Category.Stream.Category.
Require Import Category.Stream.Axioms.
Require Import Theory.Category.
Require Import Theory.InitialTerminal.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.PrecompositionWithProduct.
Require Import Theory.PushforwardComodule.

Generalizable All Variables.

(* Unset Universe Polymorphism. *)

(*------------------------------------------------------------------------------
  -- ＳＴＲＥＡＭ  ＩＳ  ＴＥＲＭＩＮＡＬ  ＩＮ  ＳＴＲＥＡＭ
  ----------------------------------------------------------------------------*)
(** * Stream is terminal in Streams **)

(* begin hide *)
Ltac clean_hyps := repeat match goal with H : _ |- _ => clear H end.
(* end hide *)

Ltac reflexivity ::= apply reflexivity || refl.

Module StreamTerminal (Import Ax : StreamAxioms).

  (** ** -∼- is an equivalence relation **)
  Lemma bisim_refl : ∀ {A} {s : Stream A}, s ∼ s.
  Proof.
    intros. apply bisim_intro with (R := λ s₁ s₂ ∙ s₁ = s₂); [clean_hyps; intros..|auto].
    - subst; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma bisim_sym : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → s₂ ∼ s₁.
  Proof.
    intros.
    apply bisim_intro with (R := λ s₁ s₂ ∙ s₂ ∼ s₁); [clean_hyps; intros..|auto].
    - symmetry; now apply bisim_head.
    - now apply bisim_tail.
  Qed.

  Lemma bisim_trans : ∀ {A} {s₁ s₂ s₃ : Stream A}, s₁ ∼ s₂ → s₂ ∼ s₃ → s₁ ∼ s₃.
  Proof.
    intros.
    apply bisim_intro with (R := λ s₁ s₃ ∙ ∃ s₂, s₁ ∼ s₂ ∧ s₂ ∼ s₃);
    [clean_hyps; intros.. | eauto].
    - destruct H as (? & ? & ?).
      etransitivity. eapply bisim_head; eauto.
      now apply bisim_head.
    - destruct H as (? & ? & ?).
      eexists; split; eapply bisim_tail; eauto.
  Qed.

  Instance bisim_equiv : ∀ {A}, Equivalence (@bisim A).
  Proof.
    constructor; repeat intro.
    - now apply bisim_refl.
    - now apply bisim_sym.
    - eapply bisim_trans; eauto.
  Qed.

  Lemma eq_bisim : ∀ {A} {s₁ s₂ : Stream A}, s₁ = s₂ → s₁ ∼ s₂.
  Proof.
    intros. now rewrite H.
  Qed.

  (** ** Stream as a setoid **)
  Program Definition STREAM (A : Type) : Setoid :=
    Setoid.make ⦃ Carrier ≔ Stream A ; Equiv ≔ bisim ⦄.

  (** ** head & tail are setoids morphisms **)
  Lemma head_cong : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. now apply bisim_head.
  Qed.

  Lemma tail_cong : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. now apply bisim_tail.
  Qed.

  Program Definition 𝒉𝒆𝒂𝒅 {A} : STREAM A ⇒ 𝑬𝑸 A := Π.make head.
  (** head-cong **)
  Next Obligation.
    now destruct (head_cong H).
  Qed.

  Definition 𝒕𝒂𝒊𝒍 {A} : Π (STREAM A) (STREAM A).
  Proof.
    refine (Π.make _); [ apply tail|].
    intros; now apply tail_cong.
  Defined.

  (** ** Cosubstitution for streams **)
  Definition cosubst {A B : 𝑻𝒚𝒑𝒆} (f : Stream A → B) : Stream A → Stream B :=
    corec f tail.

  (** ** Stream is a relative comonad over EQ **)
  Obligation Tactic := idtac.
  Program Definition 𝑺𝒕𝒓 : ‵ 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 𝑬𝑸 ′ :=
    RelativeComonad.make  ⦃ T       ≔ STREAM
                          ; counit  ≔ λ X ∙ 𝒉𝒆𝒂𝒅
                          ; cobind  ≔ λ X Y ∙ λ f ↦ Π.make (cosubst f) ⦄.
  (** cosubst-cong **)
  Next Obligation.
    intros.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x y, x ∼ y ∧ s₁ = cosubst f x ∧ s₂ = cosubst f y)
    ; [clean_hyps; intros..|eauto].
    - destruct H as (x & y & eq_xy & -> & ->).
      unfold cosubst. repeat rewrite head_corec.
      destruct f. simpl. destruct (map_cong0 _ _ eq_xy). reflexivity.
    - destruct H as (x & y & eq_xy & -> & ->).
      exists (tail x). exists (tail y).
      split; [|split].
      + now apply bisim_tail.
      + unfold cosubst at 1. rewrite tail_corec. reflexivity.
      + unfold cosubst at 1. rewrite tail_corec. reflexivity.
  Qed.
  (** cosubst-cong₂ **)
  Next Obligation.
    intros X Y f g eq_fg x. simpl.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x y, x ∼ y ∧ s₁ = cosubst f x ∧ s₂ = cosubst g y); [intros..|eauto].
    - destruct H as (x' & y' & eq_xy' & -> & ->).
      unfold cosubst; repeat rewrite head_corec.
      etransitivity. eapply (Setoids.cong f). apply eq_xy'.
      now apply eq_fg.
    - destruct H as (x' & y' & eq_xy' & -> & ->).
      exists (tail x'). exists (tail y').
      split; [|split].
      + now apply bisim_tail.
      + unfold cosubst at 1. rewrite tail_corec. reflexivity.
      + unfold cosubst at 1. rewrite tail_corec. reflexivity.
  Qed.
  (** cobind-counit **)
  Next Obligation.
    simpl. intros.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x y, x ∼ y ∧ s₁ = cosubst head x ∧ s₂ = y); [clean_hyps; intros..|eauto].
    - destruct H as (x & y & eq_xy & -> & ->).
      unfold cosubst; rewrite head_corec; now apply head_cong.
    - destruct H as (x & y & eq_xy & -> & ->).
      exists (tail x). exists (tail y).
      split; [|split].
      + now apply bisim_tail.
      + unfold cosubst at 1. rewrite tail_corec. reflexivity.
      + reflexivity.
  Qed.
  (** counit-cobind **)
  Next Obligation.
    repeat intro. rewrite H. simpl. unfold cosubst. now rewrite head_corec.
  Qed.
  (** cobind-cobind **)
  Next Obligation.
    intros X Y Z f g x y eq_xy. rewrite <- eq_xy. clear y eq_xy. simpl.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x, s₁ = cosubst g (cosubst f x) ∧ s₂ = cosubst (λ y ∙ g (cosubst f y)) x);
    [clean_hyps; intros..|eauto].
    - destruct H as (x & -> & ->).
      unfold cosubst. repeat rewrite head_corec. reflexivity.
    - destruct H as (x & -> & ->).
      exists (tail x). split.
      + unfold cosubst. now do 2 rewrite tail_corec.
      + unfold cosubst. now rewrite tail_corec.
  Qed.

  (** ** Stream coalgebra **)
  Program Definition 𝑻𝒂𝒊𝒍 : ‵ [𝑺𝒕𝒓] ⇒ [𝑺𝒕𝒓] ′ :=
    Comodule.make ⦃ α ≔ λ A ∙ Setoids.Morphism.make 𝒕𝒂𝒊𝒍 ⦄.
  (** tail-cong **)
  Next Obligation.
    intros A x y eq_xy; now rewrite eq_xy.
  Qed.
  (** α-commutes **)
  Next Obligation.
    intros C D f x y eq_xy. rewrite eq_xy. apply eq_bisim. simpl. unfold cosubst. now rewrite tail_corec.
  Qed.

  Program Definition 𝑺𝑻𝑹 : ‵ 𝑺𝒕𝒓𝒆𝒂𝒎 ′ :=
    Stream.make ⦃ T ≔ 𝑺𝒕𝒓 ; tail ≔ 𝑻𝒂𝒊𝒍 ⦄.

  (** ** 𝑺𝑻𝑹 is a terminal object **)

  Section Defs.

    Variable (Tr : 𝑺𝒕𝒓𝒆𝒂𝒎).

    Notation T                  := (Stream.T Tr).
    Notation "'T⋅tail'"         := (Stream.tail Tr _).
    Notation "'T⋅tail[' A ]"    := (Stream.tail Tr A) (only parsing).
    Notation STR                := (Stream.T 𝑺𝑻𝑹).
    Notation "'STR⋅tail'"       := (Stream.tail 𝑺𝑻𝑹 _).
    Notation "'STR⋅tail[' A ]"  := (Stream.tail 𝑺𝑻𝑹 A) (only parsing).

    Local Notation "a ∼ b" := (SEquiv a b).

    Definition tau {A} : T A → STR A := corec T⋅counit T⋅tail.

    Lemma head_tau : ∀ A (t : T A), STR⋅counit (tau t) = T⋅counit t.
    Proof.
      intros. unfold tau. simpl. now rewrite head_corec.
    Qed.

    Lemma tail_tau : ∀ A (t : T A), STR⋅tail (tau t) = tau (T⋅tail t).
    Proof.
      intros. unfold tau. simpl. now rewrite tail_corec.
    Qed.

    Lemma tau_cong : ∀ A (x y : T A), x ∼ y → tau x ∼ tau y.
    Proof.
      intros.
      apply bisim_intro with (λ s₁ s₂ ∙ ∃ x y, x ∼ y ∧ s₁ = tau x ∧ s₂ = tau y);
      [clean_hyps; intros..|eauto].
      - destruct H as (x & y & eq_xy & -> & ->).
        unfold tau. repeat rewrite head_corec. now rewrite eq_xy.
      - destruct H as (x & y & eq_xy & -> & ->).
        exists (T⋅tail x). exists (T⋅tail y). split; [|split].
        + now rewrite eq_xy.
        + unfold tau. now rewrite tail_corec.
        + unfold tau. now rewrite tail_corec.
    Qed.

    Program Definition Tau {A} : T A ⇒ STR A :=
      Setoids.Morphism.make tau.
    (** tau-cong **)
    Next Obligation.
      intros. now apply tau_cong.
    Qed.

    Lemma tau_counit : ∀ A (t t' : T A), t ∼ t' → T⋅counit t ∼ STR⋅counit (tau t').
    Proof.
      intros A t t' eq_tt'. rewrite eq_tt'. simpl. unfold tau. now rewrite head_corec.
    Qed.

    Lemma tau_cobind : ∀ A B (f : STR A ⇒ 𝑬𝑸 B) x y, x ∼ y → Tau (T⋅cobind (f ∘ Tau) x) ∼ STR⋅cobind f (Tau y).
    Proof.
      intros A B f x y eq_xy. rewrite <- eq_xy. clear y eq_xy.
      apply bisim_intro with (λ s₁ s₂ ∙ ∃ x, s₁ ∼ Tau (T⋅cobind (f ∘ Tau) x) ∧ s₂ ∼ STR⋅cobind f (Tau x));
      [clean_hyps;intros..|eauto].
      - destruct H as (x & ? & ?).
        etransitivity. eapply head_cong. apply H.
        symmetry; etransitivity. eapply head_cong; apply H0.
        simpl. unfold tau, cosubst. repeat rewrite head_corec.
        symmetry. etransitivity. apply (counit_cobind T). reflexivity.
        reflexivity.
      - destruct H as (x & ? & ?).
        exists (T⋅tail x). split.
        etransitivity. eapply tail_cong. apply H.
        simpl. unfold tau. repeat rewrite tail_corec.
        apply tau_cong. etransitivity. apply (α_commutes (Stream.tail Tr)). reflexivity.
        simpl. reflexivity.
        etransitivity. eapply tail_cong. apply H0.
        simpl. unfold tau, cosubst. repeat rewrite tail_corec. reflexivity.
      - exists x; split; reflexivity.
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
    repeat intro. rewrite H. simpl. unfold tau. repeat rewrite tail_corec. reflexivity.
  Qed.

  (* begin hide *)
  Local Notation "⟨ f ⟩" := (RelativeComonad.τ (m := Stream.τ f)) (only parsing).
  (* end hide *)

  (** 𝑺𝑻𝑹 is a terminal object **)
  Program Definition Terminality : Terminal 𝑺𝒕𝒓𝒆𝒂𝒎 :=
    Terminal.make  ⦃ one  ≔ 𝑺𝑻𝑹
                   ; top  ≔ τ ⦄.
  (** top-unique **)
  Next Obligation.
    intros A f X x y eq_xy. rewrite <- eq_xy. clear y eq_xy. simpl.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x, s₁ ∼ ⟨f⟩ _ x ∧ s₂ ∼ tau A x); [clean_hyps; intros..|].
    - destruct H as (? & ? & ?).
      etransitivity. eapply head_cong. apply H.
      symmetry; etransitivity. eapply head_cong. apply H0.
      unfold tau. rewrite head_corec. symmetry. etransitivity. symmetry. apply (τ_counit (Stream.τ f)).
      reflexivity. reflexivity.
    - destruct H as (? & ? & ?).
      exists (Stream.tail A _ x). split.
      + etransitivity. eapply tail_cong. apply H.
        etransitivity. symmetry. eapply (Stream.τ_commutes f). reflexivity.
        reflexivity.
      + etransitivity. eapply tail_cong. apply H0.
        unfold tau. rewrite tail_corec. reflexivity.
    - exists x. split; reflexivity.
  Qed.

End StreamTerminal.
