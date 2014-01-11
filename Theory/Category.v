(**

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

(** 

  Content of this file:
  
  definition of category

*)

Require Export Misc.Unicode.
Require Export Theory.Notations.
Require Export Theory.SetoidType.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＣＡＴＥＧＯＲＹ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Structure Category : Type := mkCategory
{ Obj           :> Type
; Hom           :  Obj → Obj → Setoid where "A ⇒ B" := (Hom A B)
; id            :  ∀ {A}, A ⇒ A
; compose       :  ∀ {A B C}, [ B ⇒ C ⟶ A ⇒ B ⟶ A ⇒ C ] where "g ∘ f" := (compose g f)
; left_id       :  ∀ {A B} {f : A ⇒ B}, id ∘ f ≈ f
; right_id      :  ∀ {A B} {f : A ⇒ B}, f ∘ id ≈ f
; compose_assoc :  ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}, h ∘ g ∘ f ≈ h ∘ (g ∘ f) }.

Arguments mkCategory {_ _ _ _} _ _ _.
Arguments Hom        {_} _ _.
Arguments id         {_} {_}.
Arguments compose    {_} {_ _ _}.

Notation "_⇒_" := Hom (only parsing).
Infix "⇒" := Hom.

Notation "_∘_" := compose (only parsing).
Infix "∘" := compose.

Notation "'id[' X ]" := (id (A := X)) (only parsing).
Notation "T '-id'" := (id (c := T)) (at level 0, only parsing).
Notation "T '-id[' X ]" := (id (c := T) (A := X)) (at level 0, only parsing).

Notation make Hom id compose := (@mkCategory _ Hom id compose _ _ _) (only parsing).