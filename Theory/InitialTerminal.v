(**

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

(** 

  Content of this file:
  
  definition of initial and terminal object

*)

Require Import Theory.Category.

Generalizable All Variables.

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

Module Initial.

  Notation make empty bottom := (@mkInitial _ empty bottom _) (only parsing).

End Initial.



(*------------------------------------------------------------------------------
  -- ＴＥＲＭＩＮＡＬ  ＯＢＪＥＣＴ
  ----------------------------------------------------------------------------*)

Structure Terminal (𝒞 : Category) := mkTerminal
{ one :> 𝒞
; top : ∀ {A : 𝒞}, A ⇒ one
; top_unique : ∀ `{f : A ⇒ one}, f ≈ top }.

Notation "⟨⊤⟩"      := one.
Notation "!-⊤"      := top.
Notation "⊤-unique" := top_unique.

Module Terminal.

  Notation make one top := (@mkTerminal _ one top _) (only parsing).

End Terminal.
