(*

   Benedikt Ahrens and Régis Spadotti

   Coinitial semantics for redecoration of triangular matrices

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of initial and terminal object

*)

Require Import Theory.Category.

Generalizable All Variables.

(** ** Initial object definition **)

(*------------------------------------------------------------------------------
  -- ＩＮＩＴＩＡＬ  ＯＢＪＥＣＴ
  ----------------------------------------------------------------------------*)

Structure Initial (𝒞 : Category) := mkInitial
{ empty :> 𝒞
; bottom : ∀ {A : 𝒞}, empty ⇒ A
; bottom_unique : ∀ `{f : empty ⇒ A}, f ≈ bottom }.

Notation "⟨⊥⟩"      := empty.
Notation "!-⊥"      := bottom.
Notation "⊥-unique" := bottom_unique.

Notation "'Initial.make' ⦃ 'empty' ≔ empty ; 'bottom' ≔ bottom ⦄" :=
  (@mkInitial _ empty bottom _) (only parsing).

(*------------------------------------------------------------------------------
  -- ＴＥＲＭＩＮＡＬ  ＯＢＪＥＣＴ
  ----------------------------------------------------------------------------*)
(** ** Terminal object definition **)

Structure Terminal (𝒞 : Category) := mkTerminal
{ one :> 𝒞
; top : ∀ {A : 𝒞}, A ⇒ one
; top_unique : ∀ `{f : A ⇒ one}, f ≈ top }.

Notation "⟨⊤⟩"      := one.
Notation "!-⊤"      := top.
Notation "⊤-unique" := top_unique.

Notation "'Terminal.make' ⦃ 'one' ≔ one ; 'top' ≔ top ⦄" := (@mkTerminal _ one top _) (only parsing).
