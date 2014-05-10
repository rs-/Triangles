Require Import Coq.Relations.Relations.
Require Import Relations.Relation_Operators.
Require Import Category.Types.
Require Import Category.Setoids.
Require Import Category.Types_Setoids.
Require Import Category.CoAlg.

Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.Product.
Require Import Theory.Isomorphism.
Require Import Theory.InitialTerminal.
Require Import Theory.CoAlgebra.


(*------------------------------------------------------------------------------
  -- ＡＸＩＯＭＡＴＩＺＡＴＩＯＮ  ＯＦ  ＳＴＲＥＡＭＳ
  ----------------------------------------------------------------------------*)

Module Type StreamAxioms.

  (** ** Stream type and destructors **)
  Axiom Stream : Type → Type.
  Axiom head : ∀ {A}, Stream A → A.
  Axiom tail : ∀ {A}, Stream A → Stream A.

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

  (** ** Corecursor on Stream and computation rules **)
  Axiom corec : ∀ {A T}, (T → A) → (T → T) → T → Stream A.
  Axiom head_corec : ∀ {A T} {hd : T → A} {tl : T → T} {t}, head (corec hd tl t) = hd t.
  Axiom tail_corec : ∀ {A T} {hd : T → A} {tl : T → T} {t}, tail (corec hd tl t) ∼ corec hd tl (tl t).

End StreamAxioms.

(*------------------------------------------------------------------------------
  -- ＳＴＲＥＡＭ  ＥＮＤＯＦＵＮＣＴＯＲ
  ----------------------------------------------------------------------------*)

Module StreamFunctor.

  Program Definition F (A : 𝑻𝒚𝒑𝒆) : Functor 𝑺𝒆𝒕𝒐𝒊𝒅 𝑺𝒆𝒕𝒐𝒊𝒅 :=
    Functor.make ⦃ F ≔ λ X ∙ 𝑬𝑸(A) × X
                 ; map ≔ λ A B ∙ λ f ↦ ⟨ π₁ , f ∘ π₂ ⟩  ⦄.
  Next Obligation.
    intros f g eq_fg a b eq_ab. split.
    - now destruct eq_ab.
    - destruct eq_ab as [_ snds]. simpl. rewrite snds.
      now apply eq_fg.
  Qed.
  Next Obligation.
    split.
    - reflexivity.
    - simpl in *. now rewrite H0.
  Qed.

End StreamFunctor.

(*------------------------------------------------------------------------------
  -- ＳＴＲＥＡＭ-ＣＯＡＬＧＥＢＲＡ  ＨＡＳ  Ａ  ＴＥＲＭＩＮＡＬ  ＯＢＪＥＣＴ
  ----------------------------------------------------------------------------*)

Module Type StreamHasTerminal.

  Parameter S : ∀ {A : 𝑻𝒚𝒑𝒆}, Terminal (𝑪𝒐𝑨𝒍𝒈 (StreamFunctor.F A)).

End StreamHasTerminal.


(*------------------------------------------------------------------------------
  -- ＳＴＲＥＡＭ  ＡＸＩＯＭＳ  ⟸ ＳＴＲＥＡＭ-ＣＯＡＬＧＥＢＲＡ ＨＡＳ
                                               Ａ  ＴＥＲＭＩＮＡＬ  ＯＢＪＥＣＴ
  ----------------------------------------------------------------------------*)

Module Terminal_Axioms (Import MT : StreamHasTerminal) : StreamAxioms.

  Import StreamFunctor.

  (* Stream Coalgebra *)
  Notation 𝑺𝒕𝒓𝒆𝒂𝒎 A := (𝑪𝒐𝑨𝒍𝒈 (F A)).
  (* Carrier of the coalgebra, i.e a setoid *)
  Notation "⌜ S ⌝" := (CoAlgebra.A _ S).

  (* The final Stream coalgebra *)
  Notation "'𝐒'" := (⟨⊤⟩ _ MT.S) (only parsing).
  Notation "'𝐒[' A ]" := (⟨⊤⟩ _ (@MT.S A)).
  (* Unique coalgebra morphism to the final object *)
  Notation "'⇒𝐒'" := (!-⊤ _ MT.S) (only parsing).
  Notation "[ A ']⇒𝐒'" := (@top _ MT.S A).

  Module Helper.

    Local Infix "∼" := (SEquiv) (at level 70).

    Section Defs.

      Context {A : 𝑻𝒚𝒑𝒆}.

      Definition head {S : 𝑺𝒕𝒓𝒆𝒂𝒎 A} : ⌜S⌝ ⇒ 𝑬𝑸(A) := π₁ ∘ α(S).
      Definition tail {S : 𝑺𝒕𝒓𝒆𝒂𝒎 A} : ⌜S⌝ ⇒ ⌜S⌝ := π₂ ∘ α(S).

    End Defs.

  End Helper.

  (** ** Stream type and destructors **)
  Definition Stream : Type → Type := λ A ∙ ⌜𝐒[A]⌝.
  Definition head {A} : Stream A → A := Helper.head.
  Definition tail {A} : Stream A → Stream A := Helper.tail.

  (** ** Equivalence relation on streams **)
  Definition bisim {A} : Stream A → Stream A → Prop := SEquiv (o := ⌜𝐒[A]⌝).
  Infix "∼" := bisim (at level 70).

  (** ** Bisimulation elimination rules **)
  Lemma bisim_head : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. unfold head. now rewrite eq_s₁s₂.
  Qed.
  Lemma bisim_tail : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. unfold tail. now rewrite eq_s₁s₂.
  Qed.
  Notation "_∼_" := bisim (only parsing).
  Notation "∼-head" := bisim_head (only parsing).
  Notation "∼-tail" := bisim_tail (only parsing).

  Section Bisim_Intro.

    Variables (A : Type) (R : Stream A → Stream A → Prop)
              (R_head : ∀ s₁ s₂, R s₁ s₂ → head s₁ = head s₂)
              (R_tail : ∀ s₁ s₂, R s₁ s₂ → R (tail s₁) (tail s₂)).

    Notation 𝑺𝒕𝒓𝒆𝒂𝒎 := (𝑺𝒕𝒓𝒆𝒂𝒎 A).

    Definition bisim_R := clos_refl_sym_trans _ (union _ _∼_ R).

    Notation "_≃_" := bisim_R (only parsing).
    Infix "≃" := bisim_R (at level 70).

    Tactic Notation "is-∼" := apply rst_step; left.
    Tactic Notation "is-R" := apply rst_step; right.

    Instance bisim_R_equiv : Equivalence _≃_.
    Proof.
      constructor.
      - repeat intro. apply rst_refl.
      - repeat intro. now apply rst_sym.
      - repeat intro. eapply rst_trans; eauto.
    Qed.

    Program Definition TSetoid : ‵ 𝑺𝒆𝒕𝒐𝒊𝒅 ′ :=
      Setoids.make ⦃ Carrier ≔ Stream A ; Equiv ≔ _≃_ ⦄.
    Notation "'⌜𝐓⌝'" := TSetoid (only parsing).

    Program Definition 𝐓_head : ‵ ⌜𝐓⌝ ⇒ 𝑬𝑸(A) ′ := Setoids.Morphism.make head.
    Next Obligation.
      induction H.
      - destruct H.
        + now apply ∼-head.
        + now apply R_head.
      - reflexivity.
      - now symmetry.
      - etransitivity; eauto.
    Qed.

    Program Definition 𝐓_tail : ‵ ⌜𝐓⌝ ⇒ ⌜𝐓⌝ ′ := Setoids.Morphism.make tail.
    Next Obligation.
      induction H.
      - destruct H.
        + is-∼. now apply ∼-tail.
        + is-R. now apply R_tail.
      - is-∼; reflexivity.
      - now apply rst_sym.
      - eapply rst_trans; eauto.
    Qed.

    Program Definition T : ‵ 𝑺𝒕𝒓𝒆𝒂𝒎 ′ :=
      CoAlgebra.make ⦃ A ≔ ⌜𝐓⌝ ; α ≔ ⟨ 𝐓_head , 𝐓_tail ⟩ ⦄.
    Notation 𝐓 := T.

    (* identity coalgebra morphism from the terminal object 𝐒 to 𝐓 *)
    Program Definition 𝐢𝐝 : ‵ 𝐒[A] ⇒ 𝐓 ′ := CoAlgebra.make ⦃ τ ≔ Setoids.Morphism.make (λ x ∙ x) ⦄.
    Next Obligation.
      now is-∼.
    Qed.
    Next Obligation.
      split.
      - etransitivity. eapply ∼-head; apply H.
        reflexivity.
      - is-∼. etransitivity. eapply ∼-tail; apply H.
        reflexivity.
    Qed.

    (* Unique coalgebra morphism from 𝐓 to 𝐒 *)
    Definition 𝐭𝐨𝐩 : 𝐓 ⇒ 𝐒[A] := ⇒𝐒.

    (* By finality 𝐭𝐨𝐩 is the identity coalgebra morphism *)
    Lemma 𝐭𝐨𝐩_is_id : 𝑺𝒕𝒓𝒆𝒂𝒎-id ≈ 𝐭𝐨𝐩 ∘ 𝐢𝐝.
    Proof.
      transitivity ([𝐒[A]]⇒𝐒).
      - apply top_unique.
      - symmetry. apply top_unique.
    Qed.
    Notation "𝐭𝐨𝐩≈id" := (𝐭𝐨𝐩_is_id).

    Lemma bisim_intro : ∀ x y, R x y → x ∼ y.
    Proof.
      intros x y Rxy.
      etransitivity;[|symmetry; etransitivity]; [now apply 𝐭𝐨𝐩≈id..| ].
      apply (Setoids.cong (τ 𝐭𝐨𝐩)). symmetry; now is-R.
    Qed.

  End Bisim_Intro.

  (** ** Corecursor on Stream and computation rules **)
  Section Corecursor.

    Context {A R : Type}.
    Variables (R_head : R → A) (R_tail : R → R).

    (* We give to R the structure of a Stream-Coalgebra *)
    Notation "⌜𝐑⌝" := (𝑬𝑸(R)).

    Program Definition 𝐑_head : ‵ ⌜𝐑⌝ ⇒ 𝑬𝑸(A) ′ := Setoids.Morphism.make R_head.
    Program Definition 𝐑_tail : ‵ ⌜𝐑⌝ ⇒ ⌜𝐑⌝ ′ := Setoids.Morphism.make R_tail.

    Program Definition 𝐑 : ‵ 𝑺𝒕𝒓𝒆𝒂𝒎 A ′ :=
      CoAlgebra.make ⦃ A ≔ ⌜𝐑⌝ ; α ≔ ⟨ 𝐑_head , 𝐑_tail ⟩ ⦄.

    Definition corec : R → Stream A := τ [𝐑]⇒𝐒.

  End Corecursor.

  Lemma head_corec : ∀ {A R} {hd : R → A} {tl : R → R} {t}, head (corec hd tl t) = hd t.
  Proof.
    intros A R hd tl t.
    etransitivity; [now apply (τ_commutes [𝐑 hd tl]⇒𝐒) | reflexivity].
  Qed.

  Lemma tail_corec : ∀ {A R} {hd : R → A} {tl : R → R} {t}, tail (corec hd tl t) ∼ corec hd tl (tl t).
  Proof.
    intros A R hd tl t.
    etransitivity; [now apply (τ_commutes [𝐑 hd tl]⇒𝐒) | reflexivity].
  Qed.

End Terminal_Axioms.


(*------------------------------------------------------------------------------
  -- ＳＴＲＥＡＭ  ＡＸＩＯＭＳ  ⟹ ＳＴＲＥＡＭ-ＣＯＡＬＧＥＢＲＡ ＨＡＳ
                                               Ａ  ＴＥＲＭＩＮＡＬ  ＯＢＪＥＣＴ
  ----------------------------------------------------------------------------*)
Module Axioms_Terminal (Import Ax : StreamAxioms) : StreamHasTerminal.

  Import StreamFunctor.

  (* Stream Coalgebra *)
  Notation 𝑺𝒕𝒓𝒆𝒂𝒎 A := (𝑪𝒐𝑨𝒍𝒈 (F A)).
  (* Carrier of the coalgebra, i.e a setoid *)
  Notation "⌜ S ⌝" := (CoAlgebra.A _ S).

  Notation "_∼_" := bisim (only parsing).
  Notation "_∼[ A ]_" := (@bisim A) (only parsing).

  Ltac clean_hyps := repeat match goal with H : _ |- _ => clear H end.

  (* _∼_ is an equivalence relation *)
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

  Instance bisim_equiv {A} : Equivalence _∼[A]_.
  Proof.
    constructor; repeat intro.
    - now apply bisim_refl.
    - now apply bisim_sym.
    - eapply bisim_trans; eauto.
  Qed.

  Section CoAlgebraDefinition.

    (* We give Stream A the structure of a 𝑺𝒕𝒓𝒆𝒂𝐦 coalgebra *)

    Variable (A : Type).

    (* Carrier of the coalgebra *)
    Program Definition S_ := Setoids.make ⦃ Carrier ≔ Stream A ; Equiv ≔ _∼_ ⦄.
    Notation "'⌜𝐒⌝'" := S_.

    (* Destructors *)
    Program Definition 𝐒_head : ‵ ⌜𝐒⌝ ⇒ 𝑬𝑸(A) ′ := Setoids.Morphism.make head.
    Next Obligation.
      now apply ∼-head.
    Qed.

    Program Definition 𝐒_tail : ‵ ⌜𝐒⌝ ⇒ ⌜𝐒⌝ ′ := Setoids.Morphism.make tail.
    Next Obligation.
      now apply ∼-tail.
    Qed.

    Program Definition 𝐒 : ‵ 𝑺𝒕𝒓𝒆𝒂𝒎 A ′ := CoAlgebra.make ⦃ A ≔ ⌜𝐒⌝ ; α ≔ ⟨ 𝐒_head , 𝐒_tail ⟩ ⦄.

    Variable (𝐓 : 𝑺𝒕𝒓𝒆𝒂𝒎 A).

    Definition 𝐓_head : ⌜𝐓⌝ ⇒ 𝑬𝑸(A) := π₁ ∘ α(𝐓).
    Definition 𝐓_tail : ⌜𝐓⌝ ⇒ ⌜𝐓⌝ := π₂ ∘ α(𝐓).

    (* There is a coalgebra morphism from any coalgebra 𝐓 to 𝐒 *)

    Program Definition 𝐭𝐨𝐩 : ‵ 𝐓 ⇒ 𝐒 ′ := CoAlgebra.make ⦃ τ ≔ Setoids.Morphism.make (corec 𝐓_head 𝐓_tail) ⦄.
    Next Obligation.
      set (Corec := corec 𝐓_head 𝐓_tail).
      apply bisim_intro with (R := λ s₁ s₂ ∙ ∃ x y, s₁ ∼ Corec x ∧ s₂ ∼ Corec y ∧ SEquiv x y); [clean_hyps..|].
      - intros s₁ s₂ (x & y & eq_s₁ & eq_s₂ & eq_xy). change (𝐒_head s₁ = 𝐒_head s₂). rewrite eq_s₁, eq_s₂.
        simpl. unfold Corec. do 2 rewrite head_corec. now rewrite eq_xy.
      - intros s₁ s₂ (x & y & eq_s₁ & eq_s₂ & eq_xy). exists (𝐓_tail x). exists (𝐓_tail y). repeat split.
        + change (𝐒_tail s₁ ∼ Corec (𝐓_tail x)). rewrite eq_s₁. simpl. unfold Corec.
          now rewrite tail_corec.
        + change (𝐒_tail s₂ ∼ Corec (𝐓_tail y)). rewrite eq_s₂. simpl. unfold Corec.
          now rewrite tail_corec.
        + now rewrite eq_xy.
      - exists x. exists y. now repeat split.
    Qed.
    Next Obligation.
      split.
      - rewrite head_corec. now apply (Setoids.cong 𝐓_head).
      - etransitivity. apply tail_corec. apply 𝐭𝐨𝐩_obligation_1. now apply (Setoids.cong 𝐓_tail).
    Qed.

  End CoAlgebraDefinition.

  (* 𝐒 is a terminal object *)
  Program Definition S {A} : Terminal (𝑺𝒕𝒓𝒆𝒂𝒎 A) :=
    Terminal.make ⦃ one ≔ 𝐒 A ; top ≔ 𝐭𝐨𝐩 A ⦄.
  Next Obligation.
    rewrite H; clear H x; rename y into x. rename A0 into 𝐑.
    set (Corec := corec (π₁ ∘ α(𝐑)) (π₂ ∘ α(𝐑))).
    apply bisim_intro with (R := λ s₁ s₂ ∙ ∃ x, s₁ ∼ τ f x ∧ s₂ ∼ Corec x); [clean_hyps..|].
    - intros s₁ s₂ (x & eq_s₁ & eq_s₂). change (𝐒_head _ s₁ = 𝐒_head _ s₂).
      rewrite eq_s₁, eq_s₂. simpl. unfold Corec. rewrite head_corec.
      now apply (τ_commutes f).
    - intros s₁ s₂ (x & eq_s₁ & eq_s₂). set (tx := (π₂ ∘ α(𝐑)) x). exists tx. split.
      + change (𝐒_tail _ s₁ ∼ τ f tx). rewrite eq_s₁. now apply (τ_commutes f).
      + change (𝐒_tail _ s₂ ∼ Corec tx). rewrite eq_s₂. simpl. unfold Corec.
        apply tail_corec.
    - exists x. now repeat split.
  Qed.

End Axioms_Terminal.