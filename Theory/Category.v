(*

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

(*

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
(** ** Category definition **)

Structure Category : Type := mkCategory
{ Obj            :>  Type
; Hom            :   Obj → Obj → Setoid where "A ⇒ B" := (Hom A B)
; id             :   ∀ {A}, A ⇒ A
; compose        :   ∀ {A B C}, [ B ⇒ C ⟶ A ⇒ B ⟶ A ⇒ C ] where "g ∘ f" := (compose g f)
; left_id        :   ∀ {A B} {f : A ⇒ B}, id ∘ f ≈ f
; right_id       :   ∀ {A B} {f : A ⇒ B}, f ∘ id ≈ f
; compose_assoc  :   ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}, h ∘ g ∘ f ≈ h ∘ (g ∘ f) }.

Arguments mkCategory  {_ _ _ _} _ _ _.
Arguments Hom         {_} _ _.
Arguments id          {_} {_}.
Arguments compose     {_} {_ _ _}.

Notation "_⇒_"  := Hom (only parsing).
Infix "⇒"       := Hom.

Notation "_∘_"  := compose (only parsing).
Infix "∘"       := compose.

Notation "'id[' X ]"     := (id (A := X)) (only parsing).
Notation "T '-id'"       := (id (c := T)) (at level 0, only parsing).
Notation "T '-id[' X ]"  := (id (c := T) (A := X)) (at level 0, only parsing).

Notation "'Category.make' ⦃ 'Hom' ≔ Hom ; 'id' ≔ id ; 'compose' ≔ compose ⦄" :=
  (@mkCategory _ Hom id compose _ _ _) (only parsing).


(** ** Product of categories **)

Local Notation π₁ := fst.
Local Notation π₂ := snd.

Program Definition prod_cat (𝒞 𝒟 : Category) : Category :=
  Category.make ⦃ Hom ≔ λ (A B : 𝒞 ⟨×⟩ 𝒟) ∙ Setoid.make ⦃ Carrier ≔ (π₁ A ⇒ π₁ B) ⟨×⟩ (π₂ A ⇒ π₂ B)
                                                        ; Equiv ≔ λ f g ∙ π₁ f ≈ π₁ g ∧ π₂ f ≈ π₂ g ⦄
                ; id  ≔ λ A ∙ (𝒞-id , 𝒟-id)
                ; compose ≔ λ A B C ∙ λ g f ↦₂ (π₁ g ∘ π₁ f , π₂ g ∘ π₂ f) ⦄.
Next Obligation.
  constructor.
  - intros [f₁ f₂]; split; reflexivity.
  - intros [f₁ f₂] [g₁ g₂] [eq_f₁g₁ eq_f₂g₂]; split; now symmetry.
  - intros [f₁ f₂] [g₁ g₂] [h₁ h₂] [? ?] [? ?]; split; etransitivity; eauto.
Qed.
Next Obligation.
  intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; split; now apply cong.
Qed.
Next Obligation.
  split; now rewrite left_id.
Qed.
Next Obligation.
  split; now rewrite right_id.
Qed.
Next Obligation.
  split; now rewrite compose_assoc.
Qed.

Notation "A '𝘅' B" := (prod_cat A B) (at level 20, left associativity).
Notation "'_𝘅_'" := prod_cat (only parsing).
