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

Set Universe Polymorphism.

Require Import Misc.Unicode.
Require Import Morphisms.
Require Export SetoidClass.

Generalizable All Variables.
(** * Setoid **)

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
                                                                   ; Equiv    ≔ eq ⦄.

  Notation "_≈_"         := Equiv                    (only parsing).
  Notation "x ≈ y :> T"  := (Equiv (s := T) x y)     (at level 70, y at next level, no associativity).
  Notation "x ≈ y"       := (Equiv x y)              (at level 70, no associativity).
  Notation "x ≉ y"       := (complement Equiv x y)   (at level 70, no associativity).

End Setoid.


(*------------------------------------------------------------------------------
  -- ＳＥＴＯＩＤ  ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)
(** ** Morphism between setoids **)

Module Π.

  Import Setoid.

  Structure Π (From To : Setoid) : Type := mkΠ
  { map         :>  From → To
  ; map_proper  :   Proper (_≈_ ==> _≈_) map }.

  Existing Instance map_proper.

  Lemma cong From To (f : Π From To) : ∀ x y, x ≈ y → f x ≈ f y.
  Proof.
    intros x y eq_xy; now rewrite eq_xy.
  Qed.

  Set Printing Universes.

  Program Definition setoid (From To : Setoid) : Setoid :=
    Setoid.make  ⦃ Carrier  ≔ Π From To
                 ; Equiv    ≔ λ f g ∙ ∀ x y, x ≈ y → f x ≈ g y ⦄.
  Next Obligation.
    constructor.
    - (* Reflexivity *)
      intros f x y eq_xy. now rewrite eq_xy.
    - (* Symmetry *)
      intros f g eq_fg x y eq_xy. rewrite eq_xy. symmetry. now apply eq_fg.
    - (* Transitivity *)
      intros f g h eq_fg eq_gh x y eq_xy. etransitivity; eauto.
      now apply eq_gh.
  Qed.

  Notation "[ A ⟶ B ]" := (Π A B).

  Notation make f := (@mkΠ _ _ f _) (only parsing).

  Notation "'λ' x .. y ↦ F" := (make (λ x ∙ .. (λ y ∙ F) ..))
    (at level 200, x binder, y binder, no associativity).

  Program Definition id {A} : [A ⟶ A] := make (λ x ∙ x).
  Next Obligation.
    intros f g eq_fg. exact eq_fg.
  Qed.

  Program Definition compose {A B C} (g : [B ⟶ C]) (f : [A ⟶ B]) : [A ⟶ C] := make (λ x ∙ g (f x)).
  Next Obligation.
    intros x y eq_xy. rewrite eq_xy. reflexivity.
  Qed.

End Π.

Module Π₂.

  Import Setoid.

  Structure Π₂ (A B C : Setoid) : Type := mkΠ₂
  { map          :>  A → B → C
  ; map_compose  :   Proper (_≈_ ==> _≈_ ==> _≈_) map }.

  Existing Instance map_compose.

  Lemma cong A B C (f : Π₂ A B C) : ∀ x x' y y', x ≈ x' → y ≈ y' → f x y ≈ f x' y'.
  Proof.
    intros x x' y y' eq_xx' eq_yy'; now rewrite eq_xx', eq_yy'.
  Qed.

  Notation "[ A ⟶ B ⟶ C ]" := (Π₂ A B C).

  Notation make  f := (@mkΠ₂ _ _ _ f _) (only parsing).

  Notation "'λ' x .. y ↦₂ F" := (make (λ x ∙ .. (λ y ∙ F) ..))
    (at level 200, x binder, y binder, no associativity).

End Π₂.

(*----------------------------------------------------------------------------*)

Export Setoid Π Π₂.
