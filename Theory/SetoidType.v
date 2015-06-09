(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  - definition of type of setoids and type of setoid morphisms
  - identity and composition of setoid morphisms

*)

Require Import Misc.Unicode.
Require Export CMorphisms.

Generalizable All Variables.

Set Universe Polymorphism.
Set Printing Universes.

(** * Setoid **)

(** ** polymorphic identity type **)
Inductive peq {A} (x : A) : A → Prop :=
  peq_refl : peq x x.
Arguments peq_refl {_ _}, {_} _.


(*------------------------------------------------------------------------------
  -- ＳＥＴＯＩＤ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)
(** ** Setoid definiton **)

Module Setoid.

  Structure Setoid : Type := mkSetoid
  { Carrier   :>  Type
  ; Equiv     :   Carrier → Carrier → Prop
  ; is_Equiv  :   Equivalence Equiv }.

  Existing Instance is_Equiv.

  Arguments Equiv {_} _ _.

  Notation "'Setoid.make' ⦃ 'Carrier' ≔ c ; 'Equiv' ≔ eq ⦄" :=
    (mkSetoid c eq _) (only parsing).

  Program Definition eq_setoid (T : Type) : Setoid := Setoid.make  ⦃ Carrier  ≔ T
                                                         ; Equiv    ≔ peq (A := T) ⦄.
  Next Obligation.
    constructor.
    - intros x. apply peq_refl.
    - intros x y E. destruct E. apply peq_refl.
    - intros x y z E. destruct E. intro; assumption.
  Qed.

  Notation "_≈_"         := Equiv                    (only parsing).
  Notation "x ≈ y :> T"  := (Equiv (s := T) x y)     (at level 70, y at next level, no associativity).
  Notation "x ≈ y"       := (Equiv x y)              (at level 70, no associativity).
  Notation "x ≉ y"       := (complement Equiv x y)   (at level 70, no associativity).

  Lemma refl {S : Setoid} {x : S} : x ≈ x.
  Proof.
    apply reflexivity.
  Qed.

  Lemma sym {S : Setoid} {x y : S} : x ≈ y → y ≈ x.
  Proof.
    apply symmetry.
  Qed.

  Lemma trans {S : Setoid} {x y z : S} : x ≈ y → y ≈ z → x ≈ z.
  Proof.
    apply transitivity.
  Qed.

  Ltac reflexivity ::= apply @refl.
  Ltac refl   := apply @refl.
  Ltac sym    := apply @sym.
  Ltac etrans := eapply @trans.

  Ltac rew H := first [ apply H | sym; apply H].

End Setoid.


(*------------------------------------------------------------------------------
  -- ＳＥＴＯＩＤ  ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)
(** ** Morphism between setoids **)

Module Π.

  Import Setoid.

  Structure Π (From To : Setoid) : Type := mkΠ
  { map         :>  From → To
  ; map_cong    :   ∀ {x y}, x ≈ y → map x ≈ map y }.

  (* Existing Instance map_proper. *)

  (* Lemma cong From To (f : Π From To) : ∀ x y, x ≈ y → f x ≈ f y. *)
  (* Proof. *)
  (*   intros x y eq_xy; now rewrite eq_xy. *)
  (* Qed. *)

  Ltac cong := apply map_cong.

  Program Definition setoid (From To : Setoid) : Setoid :=
    Setoid.make  ⦃ Carrier  ≔ Π From To
                 ; Equiv    ≔ λ f g ∙ ∀ x, f x ≈ g x ⦄.
  Next Obligation.
    constructor.
    - (* Reflexivity *)
      intros f x; refl.
    - (* Symmetry *)
      intros f g eq_fg x. now sym.
    - (* Transitivity *)
      intros f g h eq_fg eq_gh x. etrans; eauto.
  Qed.

  Notation "[ A ⟶ B ]" := (Π A B).

  Notation make f := (@mkΠ _ _ f _) (only parsing).

  Notation "'λ' x .. y ↦ F" := (make (λ x ∙ .. (λ y ∙ F) ..))
    (at level 200, x binder, y binder, no associativity).

  Program Definition id {A} : [A ⟶ A] := make (λ x ∙ x).

  Program Definition compose {A B C} (g : [B ⟶ C]) (f : [A ⟶ B]) : [A ⟶ C] := make (λ x ∙ g (f x)).
  Next Obligation.
    now do 2 cong.
  Qed.

End Π.

Module Π₂.

  Import Setoid.

  Structure Π₂ (A B C : Setoid) : Type := mkΠ₂
  { map   :>  A → B → C
  ; cong₂ :   ∀ {x x' y y'}, x ≈ x' → y ≈ y' → map x y ≈ map x' y' }.

  (* Existing Instance map_compose. *)

  (* Lemma cong A B C (f : Π₂ A B C) : ∀ x x' y y', x ≈ x' → y ≈ y' → f x y ≈ f x' y'. *)
  (* Proof. *)
  (*   intros x x' y y' eq_xx' eq_yy'; now rewrite eq_xx', eq_yy'. *)
  (* Qed. *)

  Ltac cong₂ := apply @cong₂.
  Ltac cong_l := apply @cong₂; [| refl].
  Ltac cong_r := apply @cong₂; [refl |].

  Notation "[ A ⟶ B ⟶ C ]" := (Π₂ A B C).

  Notation make  f := (@mkΠ₂ _ _ _ f _) (only parsing).

  Notation "'λ' x .. y ↦₂ F" := (make (λ x ∙ .. (λ y ∙ F) ..))
    (at level 200, x binder, y binder, no associativity).

End Π₂.

(*----------------------------------------------------------------------------*)

Export Setoid Π Π₂.
