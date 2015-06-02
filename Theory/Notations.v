(*------------------------------------------------------------------------------
  -- ＮＯＴＡＴＩＯＮＳ
  ----------------------------------------------------------------------------*)

Set Universe Polymorphism.

Inductive prod A B : Type :=
  pair : A -> B -> prod A B.
Arguments pair {_ _} _ _.

Definition fst {A B} (p : prod A B) :=
  let '(pair a _) := p in a.

Definition snd {A B} (p : prod A B) :=
  let '(pair _ b) := p in b.

Notation "( a , b )" := (pair a b) : type_scope.


(* -- Ｃｏｒｅ  ｎｏｔａｔｉｏｎｓ                                         -- *)
Notation "⊤" := True.
Notation "⊥" := False.
Notation "_⟨⊎⟩_" := sum (only parsing).
Infix "⟨⊎⟩" := sum (at level 25, left associativity).
Infix "⟨×⟩" := prod (at level 20, left associativity).
Notation "_⟨×⟩_" := prod (only parsing).
(** Force coercion to Type (used with program) **)
Notation "‵ T ′" := (T : Type) (only parsing).
(*----------------------------------------------------------------------------*)


(* -- Ｃａｔｅｇｏｒｙ ｎｏｔａｔｉｏｎｓ                                 - --*)
Reserved Notation "A ⇒ B" (at level 30, right associativity).
Reserved Notation "f ∘ g" (at level 40, left associativity).
Reserved Notation "⟨ f , g ⟩" (at level 0, no associativity).
(*----------------------------------------------------------------------------*)
