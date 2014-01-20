(*

   Benedikt Ahrens and Régis Spadotti

   Coinitial semantics for redecoration of triangular matrices

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  - definition of isomorphism in a category
  - somme lemmas about composition and symmetry of isos

*)

Require Import Theory.Category.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＩＳＯＭＯＲＰＨＩＳＭ  ＤＥＦＩＮＩＴＩＯＮＳ
  ----------------------------------------------------------------------------*)
(** * Isomorphism **)

(** ** Inverse of a morphism definition **)

Class IsInverse {𝒞 : Category} {A B : 𝒞} (f : A ⇒ B) (g : B ⇒ A) : Prop := mkInverse
{ iso_left  : f ∘ g ≈ id
; iso_right : g ∘ f ≈ id }.

Arguments mkInverse {_ _ _ _ _} _ _.


Definition inverse_of {𝒞 : Category} {A B : 𝒞} {g : B ⇒ A} (f : A ⇒ B) `{!IsInverse f g} : B ⇒ A := g.

Arguments inverse_of {_ _ _ _} _ {_}.

Notation "f ⁻¹" := (inverse_of f) (at level 0, no associativity).

(** ** Isomorphism between objects **)
Structure Iso {𝒞 : Category} (A B : 𝒞) := mkIso
{ iso_from    :> A ⇒ B
; iso_to      : B ⇒ A
; iso_inverse : IsInverse iso_from iso_to }.

Existing Instance iso_inverse.

Arguments mkIso    {_ _ _ _} _ _.
Arguments iso_from {_ _ _} _.
Arguments iso_to   {_ _ _} _.

Infix "≅" := Iso (at level 70).
Notation "I '⋅≅-left'":= (iso_left I) (at level 0, only parsing).
Notation "I '⋅≅-right'":= (iso_left I) (at level 0, only parsing).

Notation "'Iso.make' ⦃ 'from' ≔ from ; 'to' ≔ to ⦄" :=
  (@mkIso _ _ _ from to (mkInverse _ _)) (only parsing).

(** ** _≅_ is an equivalence relation **)
Section Iso_Equivalence.

  Context {𝒞 : Category}.

  Program Definition refl {A : 𝒞} : A ≅ A :=
    Iso.make ⦃ from ≔ id
             ; to   ≔ id ⦄.
  Next Obligation. (* iso_left *)
    now rewrite left_id.
  Qed.
  Next Obligation. (* iso_right *)
    now rewrite right_id.
  Qed.

  Program Definition sym {A B : 𝒞} (iso_AB : A ≅ B) : B ≅ A :=
    Iso.make ⦃ from ≔ iso_AB⁻¹
             ; to   ≔ iso_AB ⦄.
  Next Obligation. (* iso_left *)
    now rewrite iso_right.
  Qed.
  Next Obligation. (* iso_left *)
    now rewrite iso_left.
  Qed.

  Program Definition trans {A B C : 𝒞} (iso_AB : A ≅ B) (iso_BC : B ≅ C) : A ≅ C :=
    Iso.make ⦃ from ≔ iso_BC ∘ iso_AB
             ; to   ≔ iso_AB ⁻¹ ∘ iso_BC ⁻¹ ⦄.
  Next Obligation. (* iso_left *)
    rewrite compose_assoc; setoid_rewrite <- compose_assoc at 2.
    now rewrite iso_left, left_id, iso_left.
  Qed.
  Next Obligation. (* iso_right *)
    rewrite compose_assoc; setoid_rewrite <- compose_assoc at 2.
    now rewrite iso_right, left_id, iso_right.
  Qed.

End Iso_Equivalence.

Notation "≅-refl" := refl (only parsing).
Notation "≅-sym" := sym (only parsing).
Notation "≅-trans" := trans (only parsing).
