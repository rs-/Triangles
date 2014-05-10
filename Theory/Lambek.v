Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.CoAlgebra.
Require Import Theory.InitialTerminal.
Require Import Theory.Isomorphism.

Require Import Category.CoAlg.

(*------------------------------------------------------------------------------
  -- ＬＡＭＢＥＫ'Ｓ  ＬＥＭＭＡ
  ----------------------------------------------------------------------------*)

Section Lambek.

  Context {𝒞 : Category} {F : Functor 𝒞 𝒞} (T : Terminal (𝑪𝒐𝑨𝒍𝒈 F)).

  Let 𝐓 := ⟨⊤⟩ _ T.

  Program Definition 𝐅𝐓 : ‵ 𝑪𝒐𝑨𝒍𝒈 F ′ :=
    CoAlgebra.make ⦃ A ≔ F 𝐓
                   ; α ≔ F⋅α(𝐓) ⦄.

  Program Definition 𝐓_𝐅𝐓 : ‵ 𝐓 ⇒ 𝐅𝐓 ′ :=
    CoAlgebra.make ⦃ τ ≔ α(𝐓) ⦄.
  Next Obligation.
    reflexivity.
  Qed.

  Definition 𝐅𝐓_𝐓 : 𝐅𝐓 ⇒ 𝐓 := !-⊤ _ T.

  Program Definition Lambek : F 𝐓 ≅ 𝐓 :=
    Iso.make ⦃ from ≔ @top _ T 𝐅𝐓
             ; to ≔ α(𝐓) ⦄.
  Next Obligation.
    etransitivity. apply (@top_unique _ T _ (𝐅𝐓_𝐓 ∘ 𝐓_𝐅𝐓)).
    symmetry. apply (@top_unique _ T _ id).
  Qed.
  Next Obligation.
    etransitivity. apply (τ_commutes 𝐅𝐓_𝐓). etransitivity. symmetry. apply map_compose.
    rewrite identity.
    apply Π.cong.
    etransitivity. apply Lambek_obligation_1. reflexivity.
  Qed.

End Lambek.

