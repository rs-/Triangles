(*

   Benedikt Ahrens and Régis Spadotti

   Terminal semantics for codata types in intensional Martin-Löf type theory

   http://arxiv.org/abs/1401.1053

*)

(*

  Content of this file:

  definition of strong monoidal functor between cartesian monoidal categories

*)

Require Import Theory.Category.
Require Import Theory.Isomorphism.
Require Import Theory.Functor.
Require Import Theory.Product.

Generalizable All Variables.

Set Universe Polymorphism.

(*------------------------------------------------------------------------------
  -- ＰＲＯＤＵＣＴ-ＰＲＥＳＥＲＶＩＮＧ  ＦＵＮＣＴＯＲ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)
(** * Product-preserving functor **)

(** ** Definition **)

Section ProductPreservingFunctor.

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} (F : Functor 𝒞 𝒟).

  Definition φ (A B : 𝒞) : F (A × B) ⇒ F A × F B := ⟨ F ⋅ π₁ , F ⋅ π₂ ⟩.

  Class ProductPreservingFunctor := mkProductPreservingFunctor
  { φ_inv        : ∀ {A B}, F A × F B ⇒ F (A × B)
  ; φ_is_inverse :> ∀ {A B}, IsInverse (φ A B) φ_inv }.


End ProductPreservingFunctor.

Arguments mkProductPreservingFunctor {_ _ _ _ _ _} _.
Arguments φ {_ _ _ _ _ _ _}.

Notation "'ProductPreservingFunctor.make' ⦃ 'φ' ≔ φ ⦄" :=
  (@mkProductPreservingFunctor _ _ _ _ _ φ _) (only parsing).


(** ** Equations **)

(* begin hide *)
Section equations.
(* end hide *)

  Context `{BinaryProduct 𝒞} `{BinaryProduct 𝒟} {F : Functor 𝒞 𝒟} `{!ProductPreservingFunctor F}.

  Lemma Fπ₁_φ_inv : ∀ {A B}, F ⋅ π₁ ∘ φ⁻¹ ≈ π₁[F A, F B].
  Proof.
    intros A B.
    etrans;
      [ cong₂; [ instantiate (1 := π₁ ∘ φ); unfold φ; sym; rew @π₁_compose
                       | refl ] |].
    etrans. rew compose_assoc. etrans. cong_r. rew iso_left. rew right_id.
  Qed.

  Lemma Fπ₂_φ_inv : ∀ {A B}, F ⋅ π₂ ∘ φ⁻¹ ≈ π₂[F A, F B].
  Proof.
    intros A B.
    etrans;
      [ apply cong₂; [ instantiate (1 := π₂ ∘ φ); unfold φ; sym; rew @π₂_compose
                       | reflexivity ] |].
    etrans. rew compose_assoc. etrans. cong_r. rew iso_left. rew right_id.
  Qed.

(* begin hide *)
End equations.
(* end hide *)
