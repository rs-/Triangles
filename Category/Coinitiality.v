Require Import InfiniteTriangles.redecInfiniteTriangles8_4.
Require Import Category.Setoids.
Require Import Category.Types.
Require Import Category.Types_Setoids.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Category.RComonadWithCut.
Require Import Category.TriMat.
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
  -- ＴＲＩ  ＩＳ  Ａ  ＴＥＲＭＩＮＡＬ  ＯＢＪＥＣＴ  ＯＦ  ＴＲＩＡＮＧＬＥＳ
  ----------------------------------------------------------------------------*)

Module Tri_Terminal (Import TE : Elt).

  Module Import MP := TriangleMP TE.

  (* bisimulation *)
  Local Infix "∼" := SEquiv (at level 70).

  Hint Extern 1 (fcompat (Setoids.map ?f)) =>
    (repeat intro; now apply (Setoids.cong f)).

  (**
    * 1st step: Tri is a relative comonad with over the functor 𝑬𝑸 where
    *    - counit = MP.top
    *    - cobind = MP.redec
    *    - cut    = MP.cut
    **)
  Obligation Tactic := idtac.
  Program Definition 𝑻𝒓𝒊 : RelativeComonadWithCut 𝑬𝑸 E :=
    RelativeComonadWithCut.Make
      (λ A ∙ Setoids.make (Tri A) (@bisimilar _))      (* T *)
      (λ A ∙ Setoids.Morphism.make (@top A))           (* counit *)
      (λ A B ∙ λ f ↦ Setoids.Morphism.make (redec f))  (* cobind *)
      (λ A ∙ Setoids.Morphism.make (@cut A)).          (* cut *)
  Next Obligation. (* Equivalence *)
    eauto with typeclass_instances.
  Qed.
  Next Obligation. (* counit-cong *)
    intros A x y eq_xy.
    now apply top_cong.
  Qed.
  Next Obligation. (* redec-cong *)
    intros A B f x y eq_xy.
    apply redec_cong; auto.
  Qed.
  Next Obligation. (* redec-cong₂ *)
    intros A B f g eq_fg x y eq_xy; simpl.
    etransitivity.
    - apply redec_cong; eauto.
    - apply redec_ext. intro z. now apply eq_fg.
  Qed.
  Next Obligation. (* cobind_counit *)
    intros A x y eq_xy; simpl.
    etransitivity; eauto.
    apply comonad2.
  Qed.
  Next Obligation. (* counit_cobind *)
    intros A B f x y eq_xy.
    now rewrite eq_xy.
  Qed.
  Next Obligation. (* cobind_cobind *)
    intros A B C f g x y eq_xy; simpl.
    symmetry. etransitivity. apply comonad3.
    - repeat intro; now apply (Setoids.cong g).
    - apply redec_cong; [| apply redec_cong; [| now symmetry]]; auto.
  Qed.
  Next Obligation. (* cut-cong*)
    intros A x y eq_xy; simpl.
    now apply cut_cong.
  Qed.
  Next Obligation. (* cut-counit *)
    intros A x y eq_xy; simpl.
    change (top (cut x) = snd (top y)).
    rewrite eq_xy. now apply cut_top.
  Qed.
  Next Obligation. (* cut-cobind *)
    intros A B f x y eq_xy. simpl.
    etransitivity; [ apply redec_cut |].
    apply cut_cong.
    apply redec_cong; auto.
    repeat intro. f_equal; [ f_equal | ]; now rewrite H.
  Qed.

  (**
    * 2nd step: MP.rest is a morphism of comodule 𝑻𝒓𝒊 ⇒ 𝑻𝒓𝒊(E × ─)
    **)
  Program Definition 𝑹𝒆𝒔𝒕 : ‵ [𝑻𝒓𝒊] ⇒ precomposition_with_product (F := 𝑬𝑸) E (tcomod 𝑻𝒓𝒊) ′ :=
    Comodule.Morphism.make
      (λ A ∙ Setoids.Morphism.make (@rest A)).
  Next Obligation. (* rest-cong *)
    intros A x y eq_xy. now rewrite eq_xy.
  Qed.
  Next Obligation.
    intros A B f x y eq_xy; simpl in *.
    apply redec_cong.
    - repeat intro. f_equal; [ now rewrite H | apply (Setoids.cong f); now rewrite H ].
    - now rewrite eq_xy.
  Qed.

  (**
    * 3nd step: Tri is an object in the category of Triangles
    **)
  Program Definition 𝑻𝑹𝑰 : ‵ 𝑻𝒓𝒊𝑴𝒂𝒕 E ′ :=
    TriMat.make 𝑻𝒓𝒊 𝑹𝒆𝒔𝒕.
  Next Obligation. (* α_cut *)
    intros A; repeat intro. rewrite H.
    simpl. change (rest (cut y) ~~ cut (rest y)).
    now rewrite cut_rest.
  Qed.

  (**
    * 4th step: There exists a unique morphism, from any object of 𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 to the object 𝑻𝑹𝑰
    **)
  Section Defs.

    Variable (Tr : 𝑻𝒓𝒊𝑴𝒂𝒕 E).

    Notation T                 := (TriMat.T Tr).
    Notation "'T⋅rest'"        := (TriMat.α Tr _).
    Notation "'T⋅rest[' A ]"   := (TriMat.α Tr A) (only parsing).
    Notation TRI               := (TriMat.T 𝑻𝑹𝑰).
    Notation "'TRI⋅rest'"      := (TriMat.α 𝑻𝑹𝑰 _).
    Notation "'TRI⋅rest[' A ]" := (TriMat.α 𝑻𝑹𝑰 A) (only parsing).

    CoFixpoint tau {A} (t : T A) : TRI A :=
      constr (T⋅counit t) (tau (T⋅rest t)).

    Lemma top_tau : ∀ A (t : T A), TRI⋅counit (tau t) = T⋅counit t.
      reflexivity.
    Qed.

    Lemma rest_tau : ∀ A (t : T A), TRI⋅rest (tau t) = tau (T⋅rest t).
      reflexivity.
    Qed.

    Lemma tau_cong : ∀ A (x y : T A), x ∼ y → tau x ∼ tau y.
      cofix Hc; intros A x y eq_xy. constructor.
      - simpl. now rewrite eq_xy.
      - simpl. apply Hc. now rewrite eq_xy.
    Qed.

    Program Definition Tau {A} : T A ⇒ TRI A :=
      Setoids.Morphism.make tau.
    Next Obligation.
      intros. now apply tau_cong.
    Qed.

    Lemma tau_counit : ∀ A (t t' : T A), t ∼ t' → T⋅counit t ∼ TRI⋅counit (tau t').
      intros A t t' eq_tt'. now rewrite eq_tt'.
    Qed.

    Lemma tau_cut_trans : ∀ A (x : T (E × A)) t₁ t₂, t₁ ∼ tau (T⋅cut x) → TRI⋅cut (tau x) ∼ t₂ → t₁ ∼ t₂.
    Proof.
      cofix Hc; intros A x t₁ t₂ eq_t₁ eq_t₂; constructor.
      - rewrite eq_t₁, <- eq_t₂; clear eq_t₁ eq_t₂.
        match goal with
          | H : _ |- _ = top ?x => let x' := eval simpl in x in change x with x'
        end.
        rewrite cut_top. simpl.
        simpl. etransitivity; [ apply (cut_counit T _ x) | ]; simpl; reflexivity.
      - apply Hc with (T⋅rest x); [ rewrite eq_t₁ | rewrite <- eq_t₂ ]; clear eq_t₁ eq_t₂.
        simpl. apply tau_cong. now apply (α_cut Tr).
        match goal with
          | H : _ |- _ ∼ rest ?x => let x' := eval simpl in x in change x with x'
        end. rewrite cut_rest. reflexivity.
    Qed.

    Lemma tau_cut : ∀ A (x y : T (E × A)), x ∼ y → tau (T⋅cut x) ∼ TRI⋅cut (tau y).
    Proof.
      intros.
      etransitivity; [ apply tau_cong; now rewrite H |].
      apply tau_cut_trans with y; reflexivity.
    Qed.

    Lemma tau_cobind_trans :
      ∀ A B (f : TRI A ⇒ 𝑬𝑸 B) x t₁ t₂,
        t₁ ∼ Tau (T⋅cobind (f ∘ Tau) x) → TRI⋅cobind f (Tau x) ∼ t₂ → t₁ ∼ t₂.
    Proof.
      cofix Hc; intros A B f x t₁ t₂ eq_t₁ eq_t₂; constructor.
      - rewrite eq_t₁, <- eq_t₂; clear eq_t₁ eq_t₂.
        etransitivity; [ apply top_tau |].
        etransitivity; [ apply (counit_cobind T); reflexivity |].
        reflexivity.
      - apply Hc with (f := TRI⋅extend f) (x := T⋅rest x);
        [ rewrite eq_t₁ | rewrite <- eq_t₂]; clear eq_t₁ eq_t₂.
        + apply tau_cong. etransitivity.  apply (α_commutes (TriMat.α Tr)); reflexivity.
          apply (Π.cong _ _ (T⋅cobind)); [| reflexivity ].
          intros u v eq_uv. simpl.
          f_equal. now rewrite eq_uv.
          apply (Setoids.cong f). now apply tau_cut.
        + simpl. apply redec_ext. intro t. reflexivity.
    Qed.

    Lemma tau_cobind : ∀ A B (f : TRI A ⇒ 𝑬𝑸 B) x y, x ∼ y → Tau (T⋅cobind (f ∘ Tau) x) ∼ TRI⋅cobind f (Tau y).
    Proof.
      intros A B f x y eq_xy. rewrite eq_xy.
      apply tau_cobind_trans with (f := f) (x := y); reflexivity.
    Qed.

  End Defs.

  (** τ is a morphism of triangles **)
  Program Definition τ (T : 𝑻𝒓𝒊𝑴𝒂𝒕 E) : T ⇒ 𝑻𝑹𝑰 :=
    TriMat.Morphism.make
      (RelativeComonadWithCut.Morphism.Make (λ A ∙ Tau T)).
  Next Obligation. (* τ_counit *)
    repeat intro. now apply tau_counit.
  Qed.
  Next Obligation. (* τ_cobind *)
    repeat intro. now apply tau_cobind.
  Qed.
  Next Obligation. (* τ_cut *)
    repeat intro. symmetry. apply tau_cut. now symmetry.
  Qed.
  Next Obligation. (* τ_commutes *)
    repeat intro. apply tau_cong. now rewrite H.
  Qed.

  Local Notation "⟨ f ⟩" := (RelativeComonadWithCut.τ (TriMat.τ f)) (only parsing).

  (** 𝑻𝑹𝑰 is a terminal object **)
  Program Definition Coinitiality : Terminal (𝑻𝒓𝒊𝑴𝒂𝒕 E) :=
    Terminal.make 𝑻𝑹𝑰 τ.
  Next Obligation.
    cut (∀ (T : 𝑻𝒓𝒊𝑴𝒂𝒕 E) (f g : T ⇒ 𝑻𝑹𝑰) (A : 𝑻𝒚𝒑𝒆) (t : TriMat.T T A) t₁ t₂,
           t₁ ∼ ⟨f⟩ A t → ⟨g⟩ A t ∼ t₂ → t₁ ∼ t₂); [repeat intro |].
    - rewrite H0. apply H with (f := f) (g := τ _) (t := y); reflexivity.
    - cofix Hc; intros T f g A t t₁ t₂ eq_t₁ eq_t₂; constructor.
      + rewrite eq_t₁, <- eq_t₂; clear eq_t₁ eq_t₂.
        generalize (@τ_counit); intro cc.
        etransitivity. symmetry. apply (τ_counit ⟨f⟩); reflexivity.
        symmetry.
        etransitivity. symmetry. apply (τ_counit ⟨g⟩); reflexivity.
        reflexivity.
      + eapply Hc; [ rewrite eq_t₁ | rewrite <- eq_t₂ ]; clear eq_t₁ eq_t₂.
        * symmetry. eapply (TriMat.τ_commutes f); reflexivity.
        * eapply (TriMat.τ_commutes g); reflexivity.
  Qed.

End Tri_Terminal.