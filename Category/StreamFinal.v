Require Import InfiniteTriangles.redecInfiniteTriangles8_4.
Require Import Category.Setoids.
Require Import Category.Sets.
Require Import Category.Sets_Setoids.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Category.RComonadWithCut.
Require Import Category.ITrees.
Require Import Category.Stream.
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
  -- ＩＴＲＥＥ  ＩＳ  Ａ  ＴＥＲＭＩＮＡＬ  ＯＢＪＥＣＴ  ＯＦ  ＳＴＲＥＡＭ
  ----------------------------------------------------------------------------*)

(** * Coinitiality semantics *)


Module ITree_Terminal (Import TE : Elt).

  (** ** 𝑰𝑻𝒓𝒆𝒆 is a relative comonad over 𝑬𝑸 **)

  (*
    * 1st step: Tri is a relative comonad with over the functor 𝑬𝑸 where
    *    - counit = MP.top
    *    - cobind = MP.redec
    **)
  (* FIXME refactor ITrees here *)

  (** ** 𝑻𝒂𝒊𝒍 is a morphism of comodules **)

  (*
    * 2nd step: MP.rest is a morphism of comodule 𝑰𝑻𝒓𝒆𝒆 ⇒ 𝑰𝑻𝒓𝒆𝒆
    **)
  Local Notation P := E (only parsing).

  Obligation Tactic := idtac.

  Program Definition 𝑻𝒂𝒊𝒍 (p : P) : ‵ [𝑰𝑻𝒓𝒆𝒆 P] ⇒ [𝑰𝑻𝒓𝒆𝒆 P] ′ :=
    Comodule.make ⦃ α ≔ λ A ∙ Setoids.Morphism.make (tail' p) ⦄.
  (** tail-cong **)
  Next Obligation.
    intros p A x y eq_xy. now apply tail_cong.
  Qed.
  (** rest-cong2 **)
  Next Obligation.
    intros p A B f x y eq_xy; simpl in *.
    apply redec_cong.
    - repeat intro. apply (Setoids.cong f); auto.
    - now apply tail_cong.
  Qed.

  (** ** The pair 𝑻𝑹𝑰 = (𝑻𝒓𝒊, 𝑹𝒆𝒔𝒕) is an object of the category 𝑻𝒓𝒊𝑴𝒂𝒕 **)
  (*
    * 3nd step: Tri is an object in the category of Triangles
    **)
  Program Definition 𝑰𝑻𝑹𝑬𝑬 : ‵ 𝑺𝒕𝒓𝒆𝒂𝒎 P ′ :=
    Stream.make  ⦃ T     ≔ 𝑰𝑻𝒓𝒆𝒆 P
                 ; tail  ≔ 𝑻𝒂𝒊𝒍 ⦄.

  (** ** 𝑻𝑹𝑰 is the terminal object of 𝑻𝒓𝒊𝑴𝒂𝒕 **)
  (*
    * 4th step: There exists a unique morphism, from any object of 𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 to the object 𝑻𝑹𝑰
    **)
  Section Defs.

    Variable (Tr : 𝑺𝒕𝒓𝒆𝒂𝒎 P).

    Notation T                  := (Stream.T Tr).
    Notation "'T⋅tail' p"         := (Stream.tail Tr p _) (at level 0).
    Notation "'T⋅tail[' A ] p "    := (Stream.tail Tr p A) (at level 0, only parsing).
    Notation ITREE                := (Stream.T 𝑰𝑻𝑹𝑬𝑬).
    Notation "'ITREE⋅tail' p"       := (Stream.tail 𝑰𝑻𝑹𝑬𝑬 p _) (at level 0).
    Notation "'ITREE⋅tail[' A ] p"  := (Stream.tail 𝑰𝑻𝑹𝑬𝑬 p A) (at level 0, only parsing).

    CoFixpoint tau {A} (t : T A) : ITree P A :=
      node (T⋅counit t) (λ p ∙ tau (T⋅tail p t)).

    Lemma top_tau : ∀ A (t : T A), ITREE⋅counit (tau t) = T⋅counit t.
    Proof.
      reflexivity.
    Qed.

    Lemma tail_tau : ∀ A p (t : T A), ITREE⋅tail p (tau t) = tau (T⋅tail p t).
    Proof.
      reflexivity.
    Qed.

    Lemma tail_tau' : ∀ A p (t : T A), ITrees.tail (tau t) p = tau (T⋅tail p t).
    Proof.
      reflexivity.
    Qed.

    Program Definition Tau {A} : T A ⇒ ITREE A :=
      Setoids.Morphism.make tau.
    Next Obligation.
      cofix bisim; intros.
      constructor.
      - simpl. now rewrite H.
      - intros p. simpl. apply bisim. now rewrite H.
    Qed.


    Lemma tau_cobind_trans :
      ∀ A B (f : ITREE A ⇒ 𝑬𝑸 B) x t₁ t₂,
        t₁ ∼ Tau (T⋅cobind (f ∘ Tau) x) → ITREE⋅cobind f (Tau x) ∼ t₂ → t₁ ∼ t₂.
    Proof.
      cofix Hc; intros A B f x t₁ t₂ eq_t₁ eq_t₂; constructor.
      - etransitivity. eapply head_cong. apply eq_t₁.
        symmetry. etransitivity. eapply head_cong. rewrite <- eq_t₂. reflexivity.
        symmetry. etransitivity. apply top_tau. etransitivity. apply (counit_cobind T).
        reflexivity. reflexivity.
      - intro p. apply Hc with (A := A) (f := f) (x := T⋅tail p x).
        + etransitivity. eapply tail_cong. apply eq_t₁.
          simpl. apply (Setoids.cong Tau).
          apply (α_commutes (Stream.tail Tr p)). reflexivity.
        + symmetry. etransitivity. eapply tail_cong. symmetry. apply eq_t₂.
          simpl. apply redec_ext. intro. reflexivity.
    Qed.

  End Defs.

  (** printing τ #◯# *)

  (** ◯ is a morphism of triangles **)
  Program Definition τ (T : 𝑺𝒕𝒓𝒆𝒂𝒎 P) : T ⇒ 𝑰𝑻𝑹𝑬𝑬 :=
    Stream.make ⦃ τ ≔ RelativeComonad.make ⦃ τ ≔ λ A ∙ Tau T ⦄ ⦄.
  (** τ-counit **)
  Next Obligation.
    repeat intro. now rewrite H.
  Qed.
  (** τ-cobind **)
  Next Obligation.
    intros. intros x y eq_xy. rewrite eq_xy.
    apply tau_cobind_trans with (Tr := T) (A := C) (f := f) (x := y).
    reflexivity.
    reflexivity.
  Qed.
  (** τ-commutes **)
  Next Obligation.
    repeat intro. simpl. apply (Setoids.cong (Tau T)).
    now rewrite H.
  Qed.

  (* begin hide *)
  Local Notation "⟨ f ⟩" := (RelativeComonad.τ (m := Stream.τ f)) (only parsing).
  (* end hide *)

  (** 𝑻𝑹𝑰 is a terminal object **)
  Program Definition Coinitiality : Terminal (𝑺𝒕𝒓𝒆𝒂𝒎 E) :=
    Terminal.make  ⦃ one  ≔ 𝑰𝑻𝑹𝑬𝑬
                   ; top  ≔ τ ⦄.
  Next Obligation.
    cut (∀ (T : 𝑺𝒕𝒓𝒆𝒂𝒎 E) (f g : T ⇒ 𝑰𝑻𝑹𝑬𝑬) (A : 𝑺𝒆𝒕) (t : Stream.T T A) t₁ t₂,
           t₁ ∼ ⟨f⟩ A t → ⟨g⟩ A t ∼ t₂ → t₁ ∼ t₂); [repeat intro |].
    - rewrite H0. apply H with (T := A) (f := f) (g := τ _) (t := y).
      reflexivity. reflexivity.
    - cofix Hc; intros T f g A t t₁ t₂ eq_t₁ eq_t₂; constructor.
      + etransitivity. eapply head_cong. apply eq_t₁. symmetry.
        etransitivity. eapply head_cong. symmetry. apply eq_t₂.
        etransitivity. symmetry. apply (τ_counit (Stream.τ g)). reflexivity.
        symmetry. etransitivity. symmetry. apply (τ_counit (Stream.τ f)). reflexivity.
        reflexivity.
      + intro p. eapply Hc with (T := T) (f := f) (g := g).
        etransitivity. eapply tail_cong. apply eq_t₁.
        symmetry. eapply (Stream.τ_commutes f). reflexivity.
        symmetry. etransitivity. eapply tail_cong. symmetry. apply eq_t₂. symmetry.
        eapply (Stream.τ_commutes g). reflexivity.
  Qed.

End ITree_Terminal.