Require Import Category.Setoids.
Require Import Category.Types.
Require Import Category.Types_Setoids.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Category.RComonadWithCut.
Require Import Category.TriMat.Category.
Require Import Category.TriMat.Axioms.
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

(*------------------------------------------------------------------------------
  -- ＴＲＩ  ＩＳ  ＴＥＲＭＩＮＡＬ  ＩＮ  ＴＲＩＭＡＴ
  ----------------------------------------------------------------------------*)
(** * Tri is terminal in TriMat **)

(* begin hide *)
Ltac clean_hyps := repeat match goal with H : _ |- _ => clear H end.
(* end hide *)

Lemma yyy {A : Type} {x y : A} : eq x y → peq x y.
Proof. intros. now destruct H. Qed.

Ltac reflexivity ::= apply reflexivity || refl.
Ltac equivify := match goal with
                  | [ |- ?x = ?y ] => apply xxx; change (x ≈ y)
                  | [ |- ?R ?x ?y ] => change (x ≈ y)
                  end.
Ltac etrans ::= match goal with
                  | [ |- ?x = ?y ] => apply xxx; change (x ≈ y)
                  | _ => idtac
                end; eapply trans.

Module TriMatTerminal (Import TE : Typ) (Import Ax : TriMatAxioms TE).

  Local Notation E := TE.t (only parsing).

  Local Notation coRec hd tl := (corec (λ _ ∙ hd) (λ _ ∙ tl)) (only parsing).

  (** ** -∼- is an equivalence relation **)
  Lemma bisim_refl : ∀ {A} {s : Tri A}, s ∼ s.
  Proof.
    intros. apply bisim_intro with (R := λ _ s₁ s₂ ∙ s₁ = s₂); [clean_hyps; intros..|auto].
    - subst; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma bisim_sym : ∀ {A} {s₁ s₂ : Tri A}, s₁ ∼ s₂ → s₂ ∼ s₁.
  Proof.
    intros.
    apply bisim_intro with (R := λ _ s₁ s₂ ∙ s₂ ∼ s₁); [clean_hyps; intros..|auto].
    - symmetry; now apply ∼-top.
    - now apply ∼-rest.
  Qed.

  Lemma bisim_trans : ∀ {A} {s₁ s₂ s₃ : Tri A}, s₁ ∼ s₂ → s₂ ∼ s₃ → s₁ ∼ s₃.
  Proof.
    intros.
    apply bisim_intro with (R := λ _ s₁ s₃ ∙ ∃ s₂, s₁ ∼ s₂ ∧ s₂ ∼ s₃);
    [clean_hyps; intros.. | eauto].
    - destruct H as (? & ? & ?).
      etransitivity. eapply ∼-top; eauto.
      now apply ∼-top.
    - destruct H as (? & ? & ?).
      eexists; split; eapply ∼-rest; eauto.
  Qed.

  Instance bisim_equiv : ∀ {A}, Equivalence (@bisim A).
  Proof.
    constructor; repeat intro.
    - now apply bisim_refl.
    - now apply bisim_sym.
    - eapply bisim_trans; eauto.
  Qed.

  Lemma eq_bisim : ∀ {A} {s₁ s₂ : Tri A}, s₁ = s₂ → s₁ ∼ s₂.
  Proof.
    intros. now rewrite H.
  Qed.

  (** ** Tri as a setoid **)
  Program Definition TRI (A : Type) : Setoid :=
    Setoid.make ⦃ Carrier ≔ Tri A ; Equiv ≔ bisim ⦄.

  (** ** top & rest are setoids morphisms **)
  Lemma top_cong : ∀ {A} {s₁ s₂ : Tri A}, s₁ ∼ s₂ → top s₁ = top s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. now apply ∼-top.
  Qed.

  Lemma rest_cong : ∀ {A} {s₁ s₂ : Tri A}, s₁ ∼ s₂ → rest s₁ ∼ rest s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. now apply ∼-rest.
  Qed.

  Lemma bisim_intro_bis : ∀ {A} {t₁ t₂ : Tri A}, top t₁ = top t₂ → rest t₁ ∼ rest t₂ → t₁ ∼ t₂.
  Proof.
    intros.
    apply bisim_intro with (R := λ A (s₁ s₂ : Tri A) ∙ top s₁ = top s₂ ∧ rest s₁ ∼ rest s₂);
      [ clean_hyps; intros..|].
    - tauto.
    - split. destruct H.
      + now apply top_cong.
      + destruct H.
        now apply rest_cong.
    - tauto.
  Qed.

  Program Definition 𝒕𝒐𝒑 {A} : TRI A ⇒ 𝑬𝑸 A := Π.make top.
  (** top-cong **)
  Next Obligation.
    apply yyy. now apply top_cong.
  Qed.

  Program Definition 𝒓𝒆𝒔𝒕 {A} : [ TRI A ⟶ TRI (E ⟨×⟩ A) ] := Π.make rest.
  (** rest-cong **)
  Next Obligation.
    now apply rest_cong.
  Qed.

  (** ** Redecoration for infinite triangular matrices **)
  Definition cut {A} : Tri (E ⟨×⟩ A) → Tri A := coRec (λ x ∙ snd (top x)) rest.

  Lemma top_cut : ∀ {A} {t : Tri (E ⟨×⟩ A)}, top (cut t) = snd (top t).
  Proof.
    intros. unfold cut. rewrite (top_corec (T := λ A ∙ Tri (E ⟨×⟩ A))). reflexivity.
  Qed.

  Lemma rest_cut : ∀ {A} {t : Tri (E ⟨×⟩ A)}, rest (cut t) = cut (rest t).
  Proof.
    intros. unfold cut. rewrite (rest_corec (T := λ A ∙ Tri (E ⟨×⟩ A))). reflexivity.
  Qed.

  Lemma cut_cong : ∀ {A} (x y : Tri (E ⟨×⟩ A)), x ∼ y → cut x ∼ cut y.
  Proof.
    intros.
    apply bisim_intro with (R := λ A (s₁ s₂ : Tri A) ∙ ∃ x y, x ∼ y ∧ s₁ = cut x ∧ s₂ = cut y);
    [clean_hyps;intros..|].
    - destruct H as (x & y & eq_xy & -> & ->).
      repeat rewrite top_cut. f_equal. now apply top_cong.
    - destruct H as (x & y & eq_xy & -> & ->).
      exists (rest x). exists (rest y). repeat split.
      + now apply rest_cong.
      + now apply rest_cut.
      + now apply rest_cut.
    - exists x. exists y. tauto.
  Qed.

  Definition lift {A B : Type} (f : Tri A → B) : Tri (E ⟨×⟩ A) → E ⟨×⟩ B := λ x ∙ (fst (top x) , f (cut x)).

  Lemma lift_cong :
    ∀ {A B} {f : Tri A → B}  {t₁ t₂ : Tri (E ⟨×⟩ A)},
      (∀ {t₁ t₂}, t₁ ∼ t₂ → f t₁ = f t₂) → t₁ ∼ t₂ → lift f t₁ = lift f t₂.
  Proof.
    intros.
    unfold lift. f_equal.
    - f_equal. now apply top_cong.
    - apply H. now apply cut_cong.
  Qed.

  Lemma lift_ext : ∀ {A B} {f g : Tri A → B}, (∀ x, f x = g x) → ∀ {t}, lift f t = lift g t.
  Proof.
    intros. unfold lift. f_equal. apply H.
  Qed.

  Definition redec {A B} (f : Tri A → B) (t : Tri A) : Tri B :=
    @corec (λ B ∙ { A : Type & Tri A → B & Tri A})
           (* top *)
           (λ _ t ∙ let '(existT2 _ _ A f t) := t
                    in f t)
           (* rest *)
           (λ _ t ∙ let '(existT2 _ _ A f t) := t
                    in existT2 _ _ (E ⟨×⟩ A) (lift f) (rest t))
           B (existT2 (λ A ∙ Tri A → B) (λ A ∙ Tri A) A f t).


  Lemma top_redec : ∀ {A B} (f : Tri A → B) (t : Tri A), top (redec f t) = f t.
  Proof.
    intros. unfold redec.
    now rewrite (top_corec (T := λ B ∙ {A : Type & Tri A → B & Tri A})).
  Qed.

  Lemma rest_redec : ∀ {A B} (f : Tri A → B) (t : Tri A), rest (redec f t) = redec (lift f) (rest t).
  Proof.
    intros. unfold redec.
    now rewrite (rest_corec (T := λ B ∙ {A : Type & Tri A → B & Tri A})).
  Qed.

  Lemma redec_cong:
    ∀ {A B} {f : Tri A → B} {t₁ t₂}, (∀ t₁ t₂, t₁ ∼ t₂ → f t₁ = f t₂) → t₁ ∼ t₂ → redec f t₁ ∼ redec f t₂.
  Proof.
    intros.
    apply bisim_intro
      with (R := λ B (s₁ s₂ : Tri B) ∙
                  ∃ A (x y : Tri A) f,
                      x ∼ y ∧ (∀ t₁ t₂, t₁ ∼ t₂ → f t₁ = f t₂)
                    ∧ s₁ = redec f x ∧ s₂ = redec f y); [clean_hyps; intros..|].
    - destruct H as (B & x & y & f & eq_xy & f_proper & -> & ->).
      repeat rewrite top_redec. now apply f_proper.
    - destruct H as (B & x & y & f & eq_xy & f_proper & -> & ->).
      eexists. exists (rest x). exists (rest y). exists (lift f). repeat split.
      + now apply ∼-rest.
      + intros. now apply lift_cong.
      + now apply rest_redec.
      + now apply rest_redec.
    - repeat eexists; eauto.
  Qed.

  Lemma redec_ext : ∀ {A B} {f g : Tri A → B} {t}, (∀ x, f x = g x) → redec f t ∼ redec g t.
  Proof.
    intros.
    apply bisim_intro
      with (R := λ B (s₁ s₂ : Tri B) ∙ ∃ A x (f g : Tri A → B), (∀ x, f x = g x) ∧ s₁ = redec f x ∧ s₂ = redec g x);
      [clean_hyps; intros..|].
    - destruct H as (B & x & f & g & eq_fg & -> & ->).
      repeat rewrite top_redec. apply eq_fg.
    - destruct H as (B & x & f & g & eq_fg & -> & ->).
      eexists. exists (rest x). exists (lift f). exists (lift g). repeat split.
      + intro. apply lift_ext. apply eq_fg.
      + now rewrite rest_redec.
      + now rewrite rest_redec.
    - do 2 eexists. exists f. exists g. repeat eexists; eauto.
  Qed.

  Lemma redec_cut : ∀ {A B} {f : Tri A → B} {t}, redec f (cut t) ∼ cut (redec (lift f) t).
  Proof.
    intros.
    apply bisim_intro with (R := λ B (s₁ s₂ : Tri B) ∙
                                  exists A (x : Tri (E ⟨×⟩ A)) f,
                                    s₁ = redec f (cut x) ∧ s₂ = cut (redec (lift f) x));
      [ clean_hyps; intros..|].
    - destruct H as (B & x & f & -> & ->).
      rewrite top_redec. rewrite top_cut. rewrite top_redec. reflexivity.
    - destruct H as (B & x & f & -> & ->).
      eexists. exists (rest x). exists (lift f). split.
      + rewrite rest_redec. rewrite rest_cut. reflexivity.
      + rewrite rest_cut. rewrite rest_redec. reflexivity.
    - repeat eexists.
  Qed.

  (** ** Tri is a relative comonad with cut over EQ **)
  Obligation Tactic := idtac.
  Program Definition 𝑻𝒓𝒊 : ‵ 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝒕 𝑬𝑸 E ′ :=
    RelativeComonadWithCut.make ⦃ T ≔ TRI
                                ; counit ≔ λ X ∙ 𝒕𝒐𝒑
                                ; cobind ≔ λ X Y ∙ λ f ↦ Π.make (redec f)
                                ; cut ≔ λ A ∙ Π.make cut ⦄.
  (** redec-cong **)
  Next Obligation.
    intros. apply redec_cong; auto. intros. equivify. now cong.
  Qed.
  (** redec-cong₂ **)
  Next Obligation.
    intros X Y f g eq_fg x. apply redec_ext. intro t. equivify. now apply eq_fg.
  Qed.
  (** cobind_counit **)
  Next Obligation.
    simpl. intros.
    apply bisim_intro with (λ A (s₁ s₂ : Tri A) ∙ ∃ x y, x ∼ y ∧ s₁ ∼ redec top x ∧ s₂ = y);
      [clean_hyps; intros..|].
    - destruct H as (x & y & eq_xy & eq & ->).
      etransitivity. eapply top_cong. apply eq.
      rewrite top_redec. now apply top_cong.
    - destruct H as (x & y & eq_xy & eq & ->).
      exists (rest x). exists (rest y). repeat split.
      + now apply ∼-rest.
      + eapply transitivity. eapply rest_cong. apply eq.
        rewrite rest_redec. apply redec_ext.
        intro . unfold lift. rewrite top_cut.
        intros. set (top x0). now destruct y0.
    - exists x. exists x. repeat split.
      + apply reflexivity.
      + reflexivity.
  Qed.
  (** counit-cobind **)
  Next Obligation.
    repeat intro. simpl. now rewrite top_redec.
  Qed.
  (** cobind-cobind **)
  Next Obligation.
    intros X Y Z f g x. simpl.
    apply bisim_intro with (λ Z (s₁ s₂ : Tri Z) ∙
                              ∃ X Y (x : Tri X) (f : Tri X → Y) (g : Tri Y → Z),
                                  (∀ t₁ t₂, t₁ ∼ t₂ → g t₁ = g t₂)
                                ∧ s₁ = redec g (redec f x) ∧ s₂ ∼ redec (λ y ∙ g (redec f y)) x);
    [clean_hyps; intros..|].
    - destruct H as (X & Y & x & f & g & g_prp & -> & eq).
      symmetry. etransitivity. eapply top_cong; exact eq.
      now repeat rewrite top_redec.
    - destruct H as (X & Y & x & f & g & g_prp & -> & eq).
      do 2 eexists. exists (rest x). exists (lift f). exists (lift g). repeat split.
      + intros. apply lift_cong; auto.
      + now repeat rewrite rest_redec.
      + eapply transitivity. eapply rest_cong; exact eq.
        repeat rewrite rest_redec. apply redec_ext.
        intro t. unfold lift. f_equal.
        * rewrite top_redec. reflexivity.
        * apply g_prp. apply redec_cut.
    - do 2 eexists. exists x. exists f. exists g. repeat split.
      + intros. equivify. now cong.
      + reflexivity.
  Qed.
  (** cut-cong **)
  Next Obligation.
    intros. now apply cut_cong.
  Qed.
  (** cut-counit **)
  Next Obligation.
    intros A x. simpl. apply yyy. rewrite top_cut. reflexivity.
  Qed.
  (** cut-cobind **)
  Next Obligation.
    intros A B f x. simpl.
    apply redec_cut.
  Qed.

  (** ** Tri coalgebra **)
  Program Definition 𝑹𝒆𝒔𝒕 : Comodule.Morphism ([𝑻𝒓𝒊]) ([𝑻𝒓𝒊][E×─]) :=
    Comodule.make ⦃ α ≔ λ A ∙ Π.make (@rest A) ⦄.
  (** rest-cong **)
  Next Obligation.
    intros A x y eq_xy. now apply rest_cong.
  Qed.
  (** rest-cong2 **)
  Next Obligation.
    intros A B f x.
    simpl. rewrite rest_redec. reflexivity.
  Qed.

  Program Definition 𝑪𝒖𝒕 : Comodule.Morphism ([𝑻𝒓𝒊][E×─]) ([𝑻𝒓𝒊]) :=
    Comodule.make ⦃ α ≔ λ A ∙ Π.make (@cut A) ⦄.
  (** cut-cong **)
  Next Obligation.
    intros A x y eq_xy. now apply cut_cong.
  Qed.
  (** cut-cong2 **)
  Next Obligation.
    intros A B f x.
    apply symmetry. simpl. apply redec_cut.
  Qed.

  Program Definition 𝑻𝑹𝑰 : ‵ 𝑻𝒓𝒊𝑴𝒂𝒕 E ′ :=
    TriMat.make  ⦃ T     ≔ 𝑻𝒓𝒊
                 ; rest  ≔ 𝑹𝒆𝒔𝒕 ⦄.
  (** α-cut **)
  Next Obligation.
    intros A; repeat intro. simpl.
    now rewrite rest_cut.
  Qed.

  (** ** 𝑻𝑹𝑰 is a terminal object **)
  Section Defs.

    Variable (Tr : 𝑻𝒓𝒊𝑴𝒂𝒕 E).

    Notation T                  := (TriMat.T Tr).
    Notation "'T⋅rest'"         := (TriMat.rest Tr _).
    Notation "'T⋅rest[' A ]"    := (TriMat.rest Tr A) (only parsing).
    Notation TRI                := (TriMat.T 𝑻𝑹𝑰).
    Notation "'TRI⋅rest'"       := (TriMat.rest 𝑻𝑹𝑰 _).
    Notation "'TRI⋅rest[' A ]"  := (TriMat.rest 𝑻𝑹𝑰 A) (only parsing).

    Definition tau {A} (t : T A) : TRI A := coRec T⋅counit T⋅rest t.

    Lemma top_tau : ∀ A (t : T A), top (tau t) = T⋅counit t.
    Proof.
      intros. unfold tau. simpl. rewrite @top_corec. reflexivity.
    Qed.

    Lemma rest_tau : ∀ A (t : T A), rest (tau t) = tau (T⋅rest t).
    Proof.
      intros. unfold tau. simpl. now rewrite @rest_corec.
    Qed.

    Infix "∼" := Equiv.

    Lemma tau_cong : ∀ A (x y : T A), x ∼ y → tau x ∼ tau y.
    Proof.
      intros.
      apply bisim_intro with (R := λ B (s₁ s₂ : TRI B) ∙ ∃ (x y : T B), x ∼ y ∧ s₁ = tau x ∧ s₂ = tau y);
        [clean_hyps; intros..|].
      - destruct H as (x & y & eq_xy & -> & ->).
        repeat rewrite top_tau. equivify. now cong.
      - destruct H as (x & y & eq_xy & -> & ->).
        exists (T⋅rest x). exists (T⋅rest y). repeat split.
        + now cong.
        + now rewrite rest_tau.
        + now rewrite rest_tau.
      - repeat eexists. apply H.
    Qed.

    Program Definition Tau {A} : T A ⇒ TRI A :=
      Π.make tau.
    Next Obligation.
      intros. now apply tau_cong.
    Qed.

    Lemma tau_counit : ∀ A (t t' : T A), t ∼ t' → T⋅counit t ∼ TRI⋅counit (tau t').
    Proof.
      intros A t t' eq_tt'. simpl. rewrite top_tau. equivify. now cong.
    Qed.

    Lemma tau_cut : ∀ A (x y : T (E × A)), x ∼ y → tau (T⋅cut x) ∼ TRI⋅cut (tau y).
    Proof.
      intros.
      apply bisim_intro
        with (R := λ B (s₁ s₂ : TRI B) ∙ exists (x y : T (E ⟨×⟩ B)), x ∼ y ∧ s₁ ∼ tau (T⋅cut x) ∧ s₂ = TRI⋅cut (tau y));
        [clean_hyps; intros..|].
      - destruct H as (x & y & eq_xy & eq & ->).
        etransitivity. eapply top_cong; exact eq.
        rewrite top_tau. equivify. etrans. apply (cut_counit T x).
        apply yyy.
        simpl. rewrite top_cut. rewrite top_tau. apply f_equal. equivify. now cong.
      - destruct H as (x & y & eq_xy & eq & ->).
        exists (T⋅rest x). exists (T⋅rest y). repeat split.
        + now cong.
        + eapply transitivity. eapply rest_cong; exact eq.
          rewrite rest_tau. apply tau_cong. now apply (TriMat.rest_cut Tr).
        + simpl. rewrite rest_cut. rewrite rest_tau. reflexivity.
      - repeat eexists. apply H. reflexivity.
    Qed.

    Lemma tau_cobind : ∀ A B (f : TRI A ⇒ 𝑬𝑸 B) x y, x ∼ y → Tau (T⋅cobind (f ∘ Tau) x) ∼ TRI⋅cobind f (Tau y).
    Proof.
      intros A B f x y eq_xy. etrans. cong. cong. apply eq_xy.
      clear x eq_xy. rename y into x.
      apply bisim_intro
        with (R := λ B (s₁ s₂ : TRI B) ∙
                    ∃ A (x : T A) (f : TRI A ⇒ 𝑬𝑸 B),
                      s₁ ∼ Tau (T⋅cobind (f ∘ Tau) x) ∧ s₂ = TRI⋅cobind f (Tau x));
        [clean_hyps; intros..|].
      - destruct H as (B & x & f & eq & ->).
        etransitivity. eapply top_cong; exact eq.
        etransitivity. apply top_tau.
        equivify. etrans. eapply (counit_cobind T). apply yyy.
        simpl. now rewrite top_redec.
      - destruct H as (B & x & f & eq & ->).
        eexists. exists (T⋅rest x). exists (TRI⋅extend f). repeat split.
        + eapply transitivity. eapply rest_cong; exact eq.
          simpl. rewrite rest_tau. apply tau_cong.
          eapply transitivity. apply (α_commutes (TriMat.rest Tr)).
          apply (Π.map_cong _ _ (T⋅cobind)). intros u. simpl. apply yyy. f_equal.
          f_equal. rewrite top_tau. reflexivity.
          equivify. cong. now apply tau_cut.
        + simpl. rewrite rest_redec, rest_tau. reflexivity.
      - repeat eexists. reflexivity.
    Qed.

  End Defs.

  (** printing τ #◯# *)

  (** ◯ is a morphism of triangles **)
  Program Definition τ (T : 𝑻𝒓𝒊𝑴𝒂𝒕 E) : T ⇒ 𝑻𝑹𝑰 :=
    TriMat.make ⦃ τ ≔ RelativeComonadWithCut.make ⦃ τ ≔ λ A ∙ Tau T ⦄ ⦄.
  (** τ-counit **)
  Next Obligation.
    repeat intro. now apply tau_counit.
  Qed.
  (** τ-cobind **)
  Next Obligation.
    repeat intro. now apply tau_cobind.
  Qed.
  (** τ-cut **)
  Next Obligation.
    repeat intro. apply symmetry. apply tau_cut. now apply symmetry.
  Qed.
  (** τ-commutes **)
  Next Obligation.
    repeat intro. simpl. now rewrite rest_tau.
  Qed.

  (* begin hide *)
  Local Notation "⟨ f ⟩" := (RelativeComonadWithCut.τ (TriMat.τ f)) (only parsing).
  (* end hide *)

  (** 𝑻𝑹𝑰 is a terminal object **)
  Program Definition Terminality : Terminal (𝑻𝒓𝒊𝑴𝒂𝒕 E) :=
    Terminal.make  ⦃ one  ≔ 𝑻𝑹𝑰
                   ; top  ≔ τ ⦄.
  (** top-unique **)
  Next Obligation.
    intros T f A x. simpl.
    apply bisim_intro
      with (R := λ A (s₁ s₂ : TRI A) ∙ ∃ x (f : T ⇒ 𝑻𝑹𝑰), s₁ ∼ ⟨f⟩ A x ∧ s₂ = tau T x);
      [clean_hyps; intros..|].
    - destruct H as (x & f & eq & ->).
      etransitivity. eapply top_cong; exact eq.
      rewrite top_tau. simpl. apply xxx. eapply transitivity. eapply symmetry.
      apply (τ_counit ⟨f⟩). apply reflexivity.
    - destruct H as (x & f & eq & ->).
      exists (TriMat.rest T _ x). exists f. split.
      + eapply transitivity. eapply rest_cong; exact eq.
        apply symmetry. eapply (TriMat.τ_commutes f).
      + rewrite rest_tau. reflexivity.
    - repeat eexists. reflexivity.
  Qed.

End TriMatTerminal.
