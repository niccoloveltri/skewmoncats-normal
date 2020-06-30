{-# OPTIONS --rewriting #-}

module SoundComplete where

open import Data.Empty
open import Data.Bool
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk
open import Cuts
open import Sound
open import Complete

-- Interaction of the soundness map with admissible rules, such as the
-- cut rules, Ic, let⊗.

[scut] : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
           [ A ∣ Δ ] ⇒ C → 〈 S ∣ Γ 〉 ⇒ A  → 〈 S ∣ Γ ++ Δ 〉 ⇒ C
[scut] {Δ = Δ} g f = g ∘ [ f ∣ Δ ]f 

[ccut] : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
         〈  T ∣ Δ 〉  ⇒ C  → [ I ∣ Γ ] ⇒ A →  Δ ≡ Δ₀ ++ A ∷ Δ' →
                                         〈 T ∣ Δ₀ ++ Γ ++ Δ' 〉 ⇒ C
[ccut] {T} {Γ} Δ₀ {Δ'} g f refl = g ∘ [ id ⊗ f ∘ φ T Δ₀ Γ ∣ Δ' ]f 
 
[ccut]-j : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' C : Fma} → 
         〈  T ∣ Δ 〉  ⇒ C  → [ A' ∣ Γ ] ⇒ A →  Δ ≡ Δ₀ ++ A ∷ Δ' →
                                         〈 T ∣ Δ₀ ++ A' ∷ Γ ++ Δ' 〉 ⇒ C
[ccut]-j {T} {Γ} Δ₀ {Δ'} g f refl = g ∘ [ id ⊗ f ∘ ψ [ t T ∣ Δ₀ ] _ Γ ∣ Δ' ]f 


soundIc : {S : Stp} (Γ Λ : Cxt) {Γ' : Cxt} {A C : Fma}
  → (f : S ∣ Γ' ⊢ C) (eq : Γ' ≡ Γ ++ A ∷ Λ)
  → sound (Ic Γ Λ f eq) ≐ sound (subst-cxt eq f) ∘ [ id ⊗ l ∘ α ∣ Λ ]f
soundIc Γ Λ ax eq = ⊥-elim ([]disj∷ Γ eq)
soundIc Γ Λ (uf f) eq with cases∷ Γ eq
soundIc .[] Λ {A = A} (uf f) refl | inj₁ (refl , refl , refl) =
  ass
  ∙ (refl ∘ (~ [∘∣ Λ ] _ _
            ∙ [≐∣ Λ ] (refl ∘ ~ lα
                      ∙ ~ ass
                      ∙ ((~ nl) ∘ refl) 
                      ∙ ass)
            ∙ [∘∣ Λ ] _ _))
  ∙ ~ ass
soundIc .(_ ∷ Γ₀) Λ (uf f) refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    sound (Ic Γ₀ Λ f refl) ∘ [ [ l ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Λ ]f
  ≐⟨ soundIc Γ₀ Λ f refl ∘ refl ⟩
    sound f ∘ [ id ⊗ l ∘ α ∣ Λ ]f ∘ [ [ l ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Λ ]f
  ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Λ ] _ _) ⟩
    sound f ∘ [ id ⊗ l ∘ α ∘ [ l ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] ass ⟩
    sound f ∘ [ id ⊗ l ∘ (α ∘ [ l ∣ Γ₀ ]f ⊗ id ⊗ id) ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] (refl ∘ (nα ∙ (refl ⊗ f⊗id ∘ refl))) ⟩
    sound f ∘ [ id ⊗ l ∘ ([ l ∣ Γ₀ ]f ⊗ id ∘ α) ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] (~ ass) ⟩
    sound f ∘ [ id ⊗ l ∘ [ l ∣ Γ₀ ]f ⊗ id ∘ α ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] (id⊗swap ∘ refl) ⟩
    sound f ∘ [ [ l ∣ Γ₀ ]f ⊗ id ∘ id ⊗ l ∘ α ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] ass ⟩
    sound f ∘ [ [ l ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ l ∘ α) ∣ Λ ]f
  ≐⟨ ~ (ass ∙ (refl ∘ ~ [∘∣ Λ ] _ _)) ⟩
    sound f ∘ [ [ l ∣ Γ₀ ]f ⊗ id ∣ Λ ]f ∘ [ id ⊗ l ∘ α ∣ Λ ]f
  qed≐
soundIc Γ Λ Ir eq = ⊥-elim ([]disj∷ Γ eq)
soundIc Γ Λ (⊗r {Γ = Γ₁} {Δ} f f₁) eq with cases++ Γ Γ₁ Λ Δ eq
soundIc Γ .(Γ₀ ++ Δ) (⊗r {Γ = .(Γ ++ _ ∷ Γ₀)} {Δ} f f₁) refl | inj₁ (Γ₀ , refl , refl) =
  proof≐
    sound (Ic Γ Γ₀ f refl) ⊗ sound f₁ ∘ φ' _ (Γ ++ I ∷ _ ∷ Γ₀) Δ
  ≐⟨ soundIc Γ Γ₀ f refl ⊗ refl ∘ refl ⟩
    (sound f ∘ [ id ⊗ l ∘ α ∣ Γ₀ ]f) ⊗ sound f₁ ∘ φ' _ (Γ ++ I ∷ _ ∷ Γ₀) Δ
  ≐⟨ refl ⊗ rid ∘ refl ⟩
    (sound f ∘ [ id ⊗ l ∘ α ∣ Γ₀ ]f) ⊗ (sound f₁ ∘ id) ∘ φ' _ (Γ ++ I ∷ _ ∷ Γ₀) Δ
  ≐⟨ f⊗∘ ∘ refl ⟩
    sound f ⊗ sound f₁ ∘ [ id ⊗ l ∘ α ∣ Γ₀ ]f ⊗ id ∘ φ' _ (Γ ++ I ∷ _ ∷ Γ₀) Δ
  ≐⟨ ass ⟩
    sound f ⊗ sound f₁ ∘ ([ id ⊗ l ∘ α ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ)
  ≐⟨ refl ∘ nφ' Γ₀ Δ (id ⊗ l ∘ α) ⟩
    sound f ⊗ sound f₁ ∘ (φ' _ Γ₀ Δ ∘ [ [ id ⊗ l ∘ α ∣ Γ₀ ]f ∣ Δ ]f)
  ≐⟨ ~ ass ⟩
    sound f ⊗ sound f₁ ∘ φ' _ (Γ ++ _ ∷ Γ₀) Δ ∘ [ [ id ⊗ l ∘ α ∣ Γ₀ ]f ∣ Δ ]f
  qed≐
soundIc .(Γ₁ ++ Γ₀) Λ (⊗r {Γ = Γ₁} {.(Γ₀ ++ _ ∷ Λ)} f f₁) refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    sound f ⊗ sound (Ic Γ₀ Λ f₁ refl) ∘ φ' _ Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ)
  ≐⟨ refl ⊗ soundIc Γ₀ Λ f₁ refl ∘ refl ⟩
    sound f ⊗ (sound f₁ ∘ [ id ⊗ l ∘ α ∣ Λ ]f) ∘ φ' _ Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ)
  ≐⟨ rid ⊗ refl ∘ refl ⟩
    (sound f ∘ id) ⊗ (sound f₁ ∘ [ id ⊗ l ∘ α ∣ Λ ]f) ∘ φ' _ Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ)
  ≐⟨ f⊗∘ ∘ refl ⟩
    sound f ⊗ sound f₁ ∘ id ⊗ [ id ⊗ l ∘ α ∣ Λ ]f ∘ φ' _ Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ)
  ≐⟨ ass ⟩
    sound f ⊗ sound f₁ ∘ (id ⊗ [ id ⊗ l ∘ α ∣ Λ ]f ∘ φ' _ Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ))
  ≐⟨ refl ∘ ((rid ⊗ [∘∣ Λ ] _ _ ∙ f⊗∘) ∘ refl ∙ ass) ⟩
    sound f ⊗ sound f₁ ∘ (id ⊗ [ id ⊗ l ∣ Λ ]f ∘ (id ⊗ [ α ∣ Λ ]f ∘ φ' _ Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ)))
  ≐⟨ refl ∘ (refl ∘ lem) ⟩
    sound f ⊗ sound f₁ ∘ (id ⊗ [ id ⊗ l ∣ Λ ]f ∘ (φ' _ Γ₁ (Γ₀ ++ I ⊗ _ ∷ Λ) ∘ [ α ∣ Λ ]f))
  ≐⟨ refl ∘ (~ ass) ⟩
    sound f ⊗ sound f₁ ∘ (id ⊗ [ id ⊗ l ∣ Λ ]f ∘ φ' _ Γ₁ (Γ₀ ++ I ⊗ _ ∷ Λ) ∘ [ α ∣ Λ ]f)
  ≐⟨ refl ∘ (nφ'2 Γ₁ Γ₀ Λ l ∘ refl) ⟩
    sound f ⊗ sound f₁ ∘ (φ' _ Γ₁ (Γ₀ ++ _ ∷ Λ) ∘ [ id ⊗ l ∣ Λ ]f ∘ [ α ∣ Λ ]f)
  ≐⟨ refl ∘ (ass ∙ (refl ∘ ~ [∘∣ Λ ] _ _)) ⟩
    sound f ⊗ sound f₁ ∘ (φ' _ Γ₁ (Γ₀ ++ _ ∷ Λ) ∘ [ id ⊗ l ∘ α ∣ Λ ]f)
  ≐⟨ ~ ass ⟩
    sound f ⊗ sound f₁ ∘ φ' _ Γ₁ (Γ₀ ++ _ ∷ Λ) ∘ [ id ⊗ l ∘ α ∣ Λ ]f
  qed≐
  where
    lem : id ⊗ [ α ∣ Λ ]f ∘ φ' _ Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ) ≐
      φ' _ Γ₁ (Γ₀ ++ I ⊗ _ ∷ Λ) ∘ [ α ∣ Λ ]f
    lem =
      proof≐
        id ⊗ [ α ∣ Λ ]f ∘ φ' _ Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ)
      ≐⟨ refl ∘ φ'++ _ Γ₁ Γ₀ (I ∷ _ ∷ Λ) ⟩ 
        id ⊗ [ α ∣ Λ ]f ∘ (ψ [ _ ∣ Γ₁ ] ([ I ∣ Γ₀ ] ⊗ _ ⊗ _) Λ ∘ [ α ∣ Λ ]f ∘ [ α ⊗ id ∣ Λ ]f ∘  [ φ' _ Γ₁ Γ₀ ⊗ id ⊗ id ∣ Λ ]f)
      ≐⟨ ~ ass ∙ ((~ ass ∙ ((~ ass) ∘ refl)) ∘ refl) ⟩ 
        id ⊗ [ α ∣ Λ ]f ∘ ψ [ _ ∣ Γ₁ ] ([ I ∣ Γ₀ ] ⊗ _ ⊗ _) Λ ∘ [ α ∣ Λ ]f ∘ [ α ⊗ id ∣ Λ ]f ∘  [ φ' _ Γ₁ Γ₀ ⊗ id ⊗ id ∣ Λ ]f
      ≐⟨ nψ2 Λ α ∘ refl ∘ refl ∘ refl ⟩ 
        ψ [ _ ∣ Γ₁ ] ([ I ∣ Γ₀ ] ⊗ (I ⊗ _)) Λ ∘ [ id ⊗ α ∣ Λ ]f ∘ [ α ∣ Λ ]f ∘ [ α ⊗ id ∣ Λ ]f ∘  [ φ' _ Γ₁ Γ₀ ⊗ id ⊗ id ∣ Λ ]f
      ≐⟨ (ass ∙ (ass ∙ (refl ∘ ((refl ∘ ~ [∘∣ Λ ] _ _ ∙ (~ [∘∣ Λ ] _ _)))))) ∘ refl ⟩ 
        ψ [ _ ∣ Γ₁ ] ([ I ∣ Γ₀ ] ⊗ (I ⊗ _)) Λ ∘ [ id ⊗ α ∘ (α ∘ α ⊗ id) ∣ Λ ]f ∘  [ φ' _ Γ₁ Γ₀ ⊗ id ⊗ id ∣ Λ ]f
      ≐⟨ refl ∘ [≐∣ Λ ] (~ ααα) ∘ refl ⟩ 
        ψ [ _ ∣ Γ₁ ] ([ I ∣ Γ₀ ] ⊗ (I ⊗ _)) Λ ∘ [ α ∘ α ∣ Λ ]f ∘  [ φ' _ Γ₁ Γ₀ ⊗ id ⊗ id ∣ Λ ]f
      ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Λ ] _ _ ∙ [≐∣ Λ ] ass ∙ [∘∣ Λ ] _ _)) ∙ ~ ass ⟩ 
        ψ [ _ ∣ Γ₁ ] ([ I ∣ Γ₀ ] ⊗ (I ⊗ _)) Λ ∘ [ α ∣ Λ ]f ∘ [ α ∘ φ' _ Γ₁ Γ₀ ⊗ id ⊗ id ∣ Λ ]f
      ≐⟨ refl ∘ [≐∣ Λ ] nα ⟩ 
        ψ [ _ ∣ Γ₁ ] ([ I ∣ Γ₀ ] ⊗ (I ⊗ _)) Λ ∘ [ α ∣ Λ ]f ∘ [ φ' _ Γ₁ Γ₀ ⊗ (id ⊗ id) ∘ α ∣ Λ ]f
      ≐⟨ refl ∘ ([≐∣ Λ ] (refl ⊗ f⊗id ∘ refl) ∙ [∘∣ Λ ] _ _) ∙ ~ ass ⟩ 
        ψ [ _ ∣ Γ₁ ] ([ I ∣ Γ₀ ] ⊗ (I ⊗ _)) Λ ∘ [ α ∣ Λ ]f ∘ [ φ' _ Γ₁ Γ₀ ⊗ id ∣ Λ ]f ∘ [ α ∣ Λ ]f
      ≐⟨ ~ φ'++ _ Γ₁ Γ₀ (I ⊗ _ ∷ Λ) ∘ refl ⟩ 
        φ' _ Γ₁ (Γ₀ ++ I ⊗ _ ∷ Λ) ∘ [ α ∣ Λ ]f
      qed≐
soundIc Γ Λ (Il f) refl = soundIc Γ Λ f refl
soundIc Γ Λ (⊗l f) refl = soundIc (_ ∷ Γ) Λ f refl
soundIc Γ Λ (⊗c Γ₁ Δ {J} {J'} f) eq with cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Δ) eq
soundIc Γ .(Γ₀ ++ J ⊗ J' ∷ Δ) (⊗c .(Γ ++ _ ∷ Γ₀) Δ {J} {J'} f) refl | inj₁ (Γ₀ , refl , refl) =
  proof≐
    sound (Ic Γ (Γ₀ ++ J ∷ J' ∷ Δ) f refl) ∘ [ α-1 ∣ Δ ]f
  ≐⟨ soundIc Γ (Γ₀ ++ J ∷ J' ∷ Δ) f refl ∘ refl ⟩ 
    sound f ∘ [ [ id ⊗ l ∘ α ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ α-1 ∣ Δ ]f
  ≐⟨ ass ⟩ 
    sound f ∘ ([ [ id ⊗ l ∘ α ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ α-1 ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩ 
    sound f ∘ [ [ id ⊗ l ∘ α ∣ Γ₀ ]f ⊗ id ⊗ id ∘ α-1 ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ nα-1 ∙ (refl ∘ refl ⊗ f⊗id)) ⟩ 
    sound f ∘ [ α-1 ∘ [ id ⊗ l ∘ α ∣ Γ₀ ]f ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩ 
    sound f ∘ ([ α-1 ∣ Δ ]f ∘ [ [ id ⊗ l ∘ α ∣ Γ₀ ]f ⊗ id ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound f ∘ [ α-1 ∣ Δ ]f ∘ [ [ id ⊗ l ∘ α ∣ Γ₀ ]f ⊗ id ∣ Δ ]f
  qed≐
soundIc .Γ₁ .Δ (⊗c Γ₁ Δ {J} {J'} f) refl | inj₂ ([] , refl , refl) = 
  proof≐
    sound (Ic Γ₁ (J' ∷ Δ) f refl) ∘ [ α-1 ∣ Δ ]f
  ≐⟨ soundIc Γ₁ (J' ∷ Δ) f refl ∘ refl ⟩ 
    sound f ∘ [ id ⊗ l ∘ α ∣ J' ∷ Δ ]f ∘ [ α-1 ∣ Δ ]f
  ≐⟨ ass ⟩ 
    sound f ∘ ([ id ⊗ l ∘ α ∣ J' ∷ Δ ]f ∘ [ α-1 ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩ 
    sound f ∘ [ (id ⊗ l ∘ α) ⊗ id ∘ α-1 ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] ((refl ⊗ rid ∙ f⊗∘) ∘ refl) ⟩ 
    sound f ∘ [ (id ⊗ l ⊗ id ∘ α ⊗ id) ∘ α-1 ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] lem ⟩ 
    sound f ∘ [ α-1 ∘ id ⊗ l ∘ α ∣ Δ ]f
  ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ⟩ 
    sound f ∘ ([ α-1 ∣ Δ ]f ∘ [ id ⊗ l ∘ α ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound f ∘ [ α-1 ∣ Δ ]f ∘ [ id ⊗ l ∘ α ∣ Δ ]f
  qed≐
  where
    lem : id ⊗ l ⊗ id ∘ α ⊗ id ∘ α-1 ≐ α-1 ∘ id ⊗ l ∘ α
    lem =
      proof≐
        id ⊗ l ⊗ id ∘ α ⊗ id ∘ α-1
      ≐⟨ (((~ lid ∙ (~ α-1α ∘ refl)) ∙ ass) ∘ refl ∙ ass) ∘ refl ⟩
        α-1 ∘ (α ∘ id ⊗ l ⊗ id ∘ α ⊗ id) ∘ α-1
      ≐⟨ refl ∘ (nα ∘ refl) ∘ refl ⟩
        α-1 ∘ (id ⊗ (l ⊗ id) ∘ α ∘ α ⊗ id) ∘ α-1
      ≐⟨ refl ∘ (refl ⊗ (~ lα) ∘ refl ∘ refl) ∘ refl ⟩
        α-1 ∘ (id ⊗ (l ∘ α) ∘ α ∘ α ⊗ id) ∘ α-1
      ≐⟨ refl ∘ ((rid ⊗ refl ∙ f⊗∘) ∘ refl ∘ refl) ∘ refl ⟩
        α-1 ∘ (id ⊗ l ∘ id ⊗ α ∘ α ∘ α ⊗ id) ∘ α-1
      ≐⟨ (~ ass ∙ ((~ ass ∙ (~ ass ∘ refl) ∙ ass) ∘ refl ∙ ass)) ∘ refl ⟩
        α-1 ∘ id ⊗ l ∘ (id ⊗ α ∘ α ∘ α ⊗ id) ∘ α-1
      ≐⟨ refl ∘ (ass ∙ ~ ααα) ∘ refl ⟩
        α-1 ∘ id ⊗ l ∘ (α ∘ α) ∘ α-1
      ≐⟨ ass ∙ (refl ∘ (ass ∙ (refl ∘ αα-1 ∙ ~ rid))) ⟩
        α-1 ∘ id ⊗ l ∘ α
      qed≐
soundIc .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ (⊗c Γ₁ .(Γ₀ ++ _ ∷ Λ) {J} {J'} f) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) =
  proof≐
    sound (Ic (Γ₁ ++ J ∷ J' ∷ Γ₀) Λ f refl) ∘ [ [ α-1 ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Λ ]f
  ≐⟨ soundIc (Γ₁ ++ J ∷ J' ∷ Γ₀) Λ f refl ∘ refl ⟩
    sound f ∘ [ id ⊗ l ∘ α ∣ Λ ]f ∘ [ [ α-1 ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Λ ]f
  ≐⟨ ass ⟩
    sound f ∘ ([ id ⊗ l ∘ α ∣ Λ ]f ∘ [ [ α-1 ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Λ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Λ ] _ _ ⟩
    sound f ∘ [ id ⊗ l ∘ α ∘ [ α-1 ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] ass ⟩
    sound f ∘ [ id ⊗ l ∘ (α ∘ [ α-1 ∣ Γ₀ ]f ⊗ id ⊗ id) ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] (refl ∘ nα) ⟩
    sound f ∘ [ id ⊗ l ∘ ([ α-1 ∣ Γ₀ ]f ⊗ (id ⊗ id) ∘ α) ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] (refl ∘ (refl ⊗ f⊗id ∘ refl ) ∙ ~ ass) ⟩
    sound f ∘ [ id ⊗ l ∘ [ α-1 ∣ Γ₀ ]f ⊗ id ∘ α ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] (id⊗swap ∘ refl) ⟩
    sound f ∘ [ [ α-1 ∣ Γ₀ ]f ⊗ id ∘ id ⊗ l ∘ α ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] ass ⟩
    sound f ∘ [ [ α-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ l ∘ α) ∣ Λ ]f
  ≐⟨ refl ∘ [∘∣ Λ ] _ _ ⟩
    sound f ∘ ([ [ α-1 ∣ Γ₀ ]f ⊗ id ∣ Λ ]f ∘ [ id ⊗ l ∘ α ∣ Λ ]f)
  ≐⟨ ~ ass ⟩
    sound f ∘ [ [ α-1 ∣ Γ₀ ]f ⊗ id ∣ Λ ]f ∘ [ id ⊗ l ∘ α ∣ Λ ]f
  qed≐

soundscut : {S : Stp} → {Γ : Cxt} → (Δ' : Cxt) {A C : Fma} → 
     (f : S ∣ Γ ⊢ A) → (g : just A ∣ Δ' ⊢ C) → 
               sound (scut f g) ≐ [scut] {S} {Γ} {Δ'} (sound g) (sound f)                 
soundccut-n-false : {T : Stp} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma}  → 
     (f : nothing ∣ Γ ⊢ A) → (g : T ∣ Δ ⊢ C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
            sound (ccut false Δ₀ f g p) ≐ [ccut] {T} {Γ} Δ₀ (sound g) (sound f) p
soundccut-n-true : {T : Stp} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma}  → 
     (f : nothing ∣ Γ ⊢ A) → (g : T ∣ Δ ⊢ C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
            sound (ccut true Δ₀ f g p) ≐ [ccut]-j {T} {Γ} Δ₀ (sound g) (sound f) p
soundccut-j : {b : Bool} {T : Stp} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' C : Fma}  → 
     (f : just A' ∣ Γ ⊢ A) → (g : T ∣ Δ ⊢ C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
            sound (ccut b Δ₀ f g p) ≐ [ccut]-j {T} {Γ} Δ₀ (sound g) (sound f) p
soundlet⊗-n-false : ∀{T Γ} Δ₀ Δ₁ {C J J'}
  → (f : nothing ∣ Γ ⊢ J ⊗ J') (g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
  → sound (let⊗ false Δ₀ Δ₁ f g) ≐ sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ T Δ₀ Γ ∣ Δ₁ ]f
soundlet⊗-j : ∀{b T Γ} Δ₀ Δ₁ {A C J J'}
  → (f : just A ∣ Γ ⊢ J ⊗ J') (g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
  → sound (let⊗ b Δ₀ Δ₁ f g) ≐ sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ t T ∣ Δ₀ ] A Γ ∣ Δ₁ ]f
soundlet⊗-n-true : ∀{T Γ} Δ₀ Δ₁ {C J J'}
  → (f : nothing ∣ Γ ⊢ J ⊗ J') (g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
  → sound (let⊗ true Δ₀ Δ₁ f g) ≐ sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ t T ∣ Δ₀ ] I Γ ∣ Δ₁ ]f

soundscut Δ ax g = rid ∙ (refl ∘ ~ [id∣ Δ ])
soundscut Δ (uf {Γ} f) g =
  proof≐
    sound (scut f g) ∘ [ l ∣ Γ ++ Δ ]f
  ≐⟨ soundscut Δ f g ∘ refl ⟩
    sound g ∘ [ sound f ∣ Δ ]f ∘ [ l ∣ Γ ++ Δ ]f
  ≐⟨ ass ⟩
    sound g ∘ ([ sound f ∣ Δ ]f ∘ [ [ l ∣ Γ ]f ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] (sound f) [ l ∣ Γ ]f ⟩
    sound g ∘ [ sound f ∘ [ l ∣ Γ ]f ∣ Δ ]f
  qed≐
soundscut .[] Ir ax = rid
soundscut ._ Ir (⊗r {Γ = Γ}{Δ} g g') =
  proof≐
    sound (scut Ir g) ⊗ sound g' ∘ φ' I Γ Δ
  ≐⟨ soundscut Γ Ir g ⊗ refl ∘ refl ⟩
    (sound g ∘ [ id ∣ Γ ]f) ⊗ sound g' ∘ φ' I Γ Δ
  ≐⟨ (refl ∘ [id∣ Γ ] ∙ ~ rid) ⊗ refl ∘ refl ⟩
    sound g ⊗ sound g' ∘ φ' I Γ Δ
  ≐⟨ rid ∙ (refl ∘ ~ [id∣ Γ ++ Δ ]) ⟩
    sound g ⊗ sound g' ∘ φ' I Γ Δ ∘ [ [ id ∣ Γ ]f ∣ Δ ]f
  qed≐
soundscut Δ Ir (Il g) = rid ∙ (refl ∘ ~ [id∣ Δ ])
soundscut .[] (⊗r f f') ax = ~ lid
soundscut ._ (⊗r {Γ = Γ}{Δ} f f') (⊗r {Γ = Γ'}{Δ'} g g') =
  proof≐
    sound (scut (⊗r f f') g) ⊗ sound g' ∘ φ' _ (Γ ++ Δ ++ Γ') Δ'
  ≐⟨ soundscut Γ' (⊗r f f') g ⊗ rid ∘ refl ⟩ 
    (sound g ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f) ⊗ (sound g' ∘ id) ∘ φ' _ (Γ ++ Δ ++ Γ') Δ'
  ≐⟨ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ Δ ++ Γ') Δ'
  ≐⟨ ass ⟩ 
    sound g ⊗ sound g' ∘ ([ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ Δ ++ Γ') Δ')
  ≐⟨ refl ∘ nφ' Γ' Δ' _ ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ' Δ' ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ++ Δ' ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ' Δ' ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ++ Δ' ]f
  qed≐
soundscut Δ (⊗r {Γ = Γ'}{Δ'} f f') (⊗l g) =
  proof≐
    sound (scut f (ccut false [] f' g refl))
  ≐⟨ soundscut (Δ' ++ Δ) f (ccut false [] f' g refl) ⟩
    sound (ccut false [] f' g refl) ∘ [ sound f ∣ Δ' ++ Δ ]f
  ≐⟨ soundccut-n-false [] f' g refl ∘ refl ⟩
    sound g ∘ [ id ⊗ sound f' ∘ φ' _ [] Δ' ∣ Δ ]f ∘ [ [ sound f ∣ Δ' ]f ∣ Δ ]f
  ≐⟨ ass ⟩
    sound g ∘ ([ id ⊗ sound f' ∘ φ' _ [] Δ' ∣ Δ ]f ∘ [ [ sound f ∣ Δ' ]f ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩
    sound g ∘ [ id ⊗ sound f' ∘ φ' _ [] Δ' ∘ [ sound f ∣ Δ' ]f ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] ass ⟩
    sound g ∘ [ id ⊗ sound f' ∘ (φ' _ [] Δ' ∘ [ sound f ∣ Δ' ]f) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ ~ (nφ' [] Δ' (sound f))) ⟩
    sound g ∘ [ id ⊗ sound f' ∘ (sound f ⊗ id ∘ φ' _ [] Δ') ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ass) ⟩
    sound g ∘ [ id ⊗ sound f' ∘ sound f ⊗ id ∘ φ' _ [] Δ' ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ f⊗∘ ∘ refl) ⟩
    sound g ∘ [ (id ∘ sound f) ⊗ (sound f' ∘ id) ∘ φ' _ [] Δ' ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (lid ⊗ (~ rid) ∘ refl) ⟩
    sound g ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ' Δ' ∣ Δ ]f
  qed≐  
soundscut Δ (Il f) g = soundscut Δ f g
soundscut Δ (⊗l f) g = soundscut Δ f g
soundscut .(Γ ++ _ ⊗ _ ∷ Δ) Ir (⊗c Γ Δ g) =
  soundscut (Γ ++ _ ∷ _ ∷ Δ) Ir g ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ ] _ _
            ∙ [≐∣ Δ ] (~ nα-1 ∙ (refl ∘ refl ⊗ f⊗id) )
            ∙ [∘∣ Δ ] _ _))
  ∙ ~ ass
soundscut .(Γ ++ _ ⊗ _ ∷ Δ) (⊗r f f₁) (⊗c Γ Δ g) = 
  soundscut (Γ ++ _ ∷ _ ∷ Δ) (⊗r f f₁) g ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ ] _ _
            ∙ [≐∣ Δ ] (~ nα-1 ∙ (refl ∘ refl ⊗ f⊗id) )
            ∙ [∘∣ Δ ] _ _))
  ∙ ~ ass
soundscut Δ' (⊗c Γ Δ f) g = 
  soundscut Δ' f g ∘ refl
  ∙ ass
  ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)

soundccut-n-false Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
soundccut-n-false Δ₀ f (uf g) p with  cases∷ Δ₀ p
soundccut-n-false {Γ = Γ} .[] f (uf {Γ = Δ} g) refl | inj₁ (refl , refl , refl) =
  proof≐
    sound (scut f g)
  ≐⟨ soundscut Δ f g ⟩
    sound g ∘ [ sound f ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] rid ⟩
    sound g ∘ [ sound f ∘ id ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ ~ lφ' Γ) ⟩
    sound g ∘ [ sound f ∘ (l ∘ φ nothing [] Γ) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ass) ⟩
    sound g ∘ [ sound f ∘ l ∘ φ nothing [] Γ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ nl ∘ refl) ⟩
    sound g ∘ [ l ∘ id ⊗ sound f ∘ φ nothing [] Γ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] ass ⟩
    sound g ∘ [ l ∘ (id ⊗ sound f ∘ φ nothing [] Γ) ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩
    sound g ∘ ([ l ∣ Δ ]f ∘ [ id ⊗ sound f ∘ φ nothing [] Γ ∣ Δ ]f)
  ≐⟨ ~ ass ⟩
    sound g ∘ [ l ∣ Δ ]f ∘ [ id ⊗ sound f ∘ φ nothing [] Γ ∣ Δ ]f
  qed≐
soundccut-n-false {Γ = Γ} .(_ ∷ Γ₀) {Δ'} f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    sound (ccut false Γ₀ f g refl) ∘ [ [ [ l ∣ Γ₀ ]f ∣ Γ ]f ∣ Δ' ]f
  ≐⟨ soundccut-n-false Γ₀ f g refl ∘ refl ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f ∘ [ [ [ l ∣ Γ₀ ]f ∣ Γ ]f ∣ Δ' ]f
  ≐⟨ ass ⟩ 
    sound g ∘ ([ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f ∘ [ [ [ l ∣ Γ₀ ]f ∣ Γ ]f ∣ Δ' ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ' ] _ _ ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∘ [ [ l ∣ Γ₀ ]f ∣ Γ ]f ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] ass ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ (φ' _ Γ₀ Γ ∘ [ [ l ∣ Γ₀ ]f ∣ Γ ]f) ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (refl ∘ ~ nφ' Γ₀ Γ _ ) ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ ([ l ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Γ) ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (~ ass) ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ [ l ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Γ ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (id⊗swap ∘ refl) ⟩ 
    sound g ∘ [ [ l ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] ass ⟩ 
    sound g ∘ [ [ l ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ Γ₀ Γ) ∣ Δ' ]f
  ≐⟨ refl ∘ [∘∣ Δ' ] _ _ ⟩ 
    sound g ∘ ([ [ l ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ∘ [ [ l ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f
  qed≐
soundccut-n-false Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
soundccut-n-false Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
soundccut-n-false {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
  proof≐
    sound (ccut false Δ₀ f g refl) ⊗ sound g' ∘ φ' _ Γ₀ Δ
  ≐⟨ soundccut-n-false Δ₀ f g refl ⊗ refl ∘ refl ⟩ 
    (sound g ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f) ⊗ sound g' ∘ φ' _ Γ₀ Δ
  ≐⟨ refl ⊗ rid ∙ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ
  ≐⟨ refl ∘ refl ∙ ass ⟩ 
    sound g ⊗ sound g' ∘ ([ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ)
  ≐⟨ refl ∘ nφ' Γ₀ Δ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ∣ Δ ]f
  qed≐
soundccut-n-false {Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    sound g ⊗ sound (ccut false Γ₀ f g' refl) ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
  ≐⟨ refl ⊗ soundccut-n-false Γ₀ f g' refl ∘ refl ⟩ 
    sound g ⊗ (sound g' ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f) ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
  ≐⟨ rid ⊗ refl ∙ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
  ≐⟨ refl ∘ (refl ⊗ [∘∣ Δ' ] _ _ ∙ (rid ⊗ refl ∙ f⊗∘)) ∙ ~ ass ∘ refl ∙ ass ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (id ⊗ [ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ'))
  ≐⟨ refl ∘ assφ' Γ Γ₀ Γ₁ Δ' ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f)
  ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩ 
    sound g ⊗ sound g' ∘ (id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ')) ∘ [ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f
  ≐⟨ refl ∘ nφ'2 Γ Γ₀ Δ' (sound f) ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∣ Δ' ]f) ∘ [ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f
  ≐⟨ ~ ass ∘ refl ∙ ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)  ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∘ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f
  qed≐
soundccut-n-false Δ₀ f (Il g) refl = soundccut-n-false Δ₀ f g refl
soundccut-n-false Δ₀ f (⊗l g) refl = soundccut-n-false (_ ∷ Δ₀) f g refl
soundccut-n-false {Γ = Γ₁} Δ₀ {Δ'} f (⊗c Γ Δ g) p with cases++ Δ₀ Γ Δ' (_ ∷ Δ) p
soundccut-n-false {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
  soundccut-n-false Δ₀ f g refl ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ ] _ _
            ∙ [≐∣ Δ ] (~ (refl ∘ refl ⊗ (~ f⊗id) ∙ nα-1))
            ∙ [∘∣ Δ ] _ _))
  ∙ ~ ass
soundccut-n-false {Γ = Γ₁} .Γ {.Δ} f (⊗c Γ Δ g) refl | inj₂ ([] , refl , refl) = soundlet⊗-n-false Γ Δ f g
soundccut-n-false {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
  soundccut-n-false (Γ ++ _ ∷ _ ∷ Γ₀) f g refl ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ' ] _ _
            ∙ [≐∣ Δ' ] lem
            ∙ [∘∣ Δ' ] _ _))
  ∙ ~ ass
  where
    lem : id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ _ ∷ Γ₀) Γ₁ ∘ [ [ α-1 ∣ Γ₀ ]f ∣ Γ₁ ]f ≐
          [ α-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁)
    lem =
      proof≐
        id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ _ ∷ Γ₀) Γ₁ ∘ [ [ α-1 ∣ Γ₀ ]f ∣ Γ₁ ]f
      ≐⟨ ass ⟩ 
        id ⊗ sound f ∘ (φ' _ (Γ ++ _ ∷ _ ∷ Γ₀) Γ₁ ∘ [ [ α-1 ∣ Γ₀ ]f ∣ Γ₁ ]f)
      ≐⟨ refl ∘ (~ (nφ' Γ₀ Γ₁ (α-1))) ⟩ 
        id ⊗ sound f ∘ ([ α-1 ∣ Γ₀ ]f ⊗ id ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁)
      ≐⟨ ~ ass ⟩ 
        id ⊗ sound f ∘ [ α-1 ∣ Γ₀ ]f ⊗ id ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁
      ≐⟨ id⊗swap ∘ refl ⟩ 
        [ α-1 ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁
      ≐⟨ ass ⟩ 
        [ α-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁)
      qed≐

soundccut-j Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
soundccut-j {Γ = Γ} [] f (uf {Δ} g) refl = 
  proof≐
    sound (scut f g) ∘ [ [ l ∣ Γ ]f ∣ Δ ]f
  ≐⟨ soundscut Δ f g ∘ refl ⟩
    sound g ∘ [ sound f ∣ Δ ]f ∘ [ [ l ∣ Γ ]f ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ lψ Γ) ⟩
    sound g ∘ [ sound f ∣ Δ ]f ∘ [ l ∘ ψ I _ Γ ∣ Δ ]f
  ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _ ∙ [≐∣ Δ ] (~ ass))) ⟩
    sound g ∘ [ sound f ∘ l ∘ ψ I _ Γ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ nl ∘ refl ∙ ass) ⟩
    sound g ∘ [ l ∘ (id ⊗ sound f ∘ ψ I _ Γ) ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩
    sound g ∘ ([ l ∣ Δ ]f ∘ [ id ⊗ sound f ∘ ψ I _ Γ ∣ Δ ]f)
  ≐⟨ ~ ass ⟩
    sound g ∘ [ l ∣ Δ ]f ∘ [ id ⊗ sound f ∘ ψ I _ Γ ∣ Δ ]f
  qed≐
soundccut-j {Γ = Γ} (x ∷ Δ₀) {Δ'} f (uf g) refl =
  soundccut-j Δ₀ f g refl ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ' ] _ _
            ∙ [≐∣ Δ' ] (((ass ∙ (refl ∘ (~ nψ Γ [ l ∣ Δ₀ ]f)) ∙ ~ ass) ∙ (id⊗swap ∘ refl)) ∙ ass)
            ∙ [∘∣ Δ' ] _ _ ))
  ∙ ~ ass
soundccut-j Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
soundccut-j Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
soundccut-j {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
  proof≐
    sound (ccut _ Δ₀ f g refl) ⊗ sound g' ∘ φ' _ Γ₀ Δ
  ≐⟨ soundccut-j Δ₀ f g refl ⊗ refl ∘ refl ⟩ 
    (sound g ∘ [ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f) ⊗ sound g' ∘ φ' _ Γ₀ Δ
  ≐⟨ refl ⊗ rid ∙ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ [ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ
  ≐⟨ refl ∘ refl ∙ ass ⟩ 
    sound g ⊗ sound g' ∘ ([ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ)
  ≐⟨ refl ∘ nφ' Γ₀ Δ (id ⊗ sound f ∘ ψ _ _ Γ) ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f ∣ Δ ]f
  qed≐
soundccut-j {Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    sound g ⊗ sound (ccut _ Γ₀ f g' refl) ∘ φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
  ≐⟨ refl ⊗ soundccut-j Γ₀ f g' refl ∘ refl ⟩ 
    sound g ⊗ (sound g' ∘ [ id ⊗ sound f ∘ ψ _ _ Γ₁ ∣ Δ' ]f) ∘ φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
  ≐⟨ rid ⊗ refl ∙ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∘ ψ _ _ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
  ≐⟨ refl ∘ (refl ⊗ [∘∣ Δ' ] _ _ ∙ (rid ⊗ refl ∙ f⊗∘)) ∙ ~ ass ∘ refl ∙ ass ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (id ⊗ [ ψ _ _ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ'))
  ≐⟨ refl ∘ lem ⟩
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f)
  ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩ 
    sound g ⊗ sound g' ∘ (id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ')) ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
  ≐⟨ refl ∘ nφ'2 Γ Γ₀ Δ' (sound f) ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∣ Δ' ]f) ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
  ≐⟨ ~ ass ∘ refl ∙ ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)  ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∘ ψ _ _ Γ₁ ∣ Δ' ]f
  qed≐
  where
  lem : id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘  φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
        ≐ φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
  lem =
    proof≐
      id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘  φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
    ≐⟨ ~ ass ⟩
      id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘ ψ _ I (Γ₀ ++ _ ∷ Γ₁ ++ Δ') ∘ [ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ ψ++ _ _ (Γ₀ ++ _ ∷ Γ₁) Δ' ∘ refl ⟩
      id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘ (ψ [ _ ∣ Γ ] [ I ∣ Γ₀ ++ _ ∷ Γ₁ ] Δ' ∘ [ ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Γ₁) ∣ Δ' ]f) ∘ [ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ (~ ass) ∘ refl ⟩
      (id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘ ψ [ _ ∣ Γ ] [ I ∣ Γ₀ ++ _ ∷ Γ₁ ] Δ') ∘ [ ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Γ₁) ∣ Δ' ]f ∘ [ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ nψ2 Δ' (ψ [ I ∣ Γ₀ ] _ Γ₁) ∘ refl ∘ refl ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ id ⊗ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘ [ ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Γ₁) ∣ Δ' ]f ∘ [ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _) ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _) ∙ (refl ∘ [≐∣ Δ' ] (~ ass)) ) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ id ⊗ ψ [ I ∣ Γ₀ ] _ Γ₁ ∘ ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Γ₁) ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] (refl ∘ ψ++ _ _ Γ₀ (_ ∷ Γ₁) ∘ refl) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ id ⊗ ψ [ I ∣ Γ₀ ] _ Γ₁ ∘ (ψ [ _ ∣ Γ ] _ Γ₁ ∘ [ α ∣ Γ₁ ]f ∘ [ ψ [ _ ∣ Γ ] I Γ₀ ⊗ id ∣ Γ₁ ]f) ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] ((~ ass ∙ ((~ ass) ∘ refl)) ∘ refl) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ id ⊗ ψ [ I ∣ Γ₀ ] _ Γ₁ ∘ ψ [ _ ∣ Γ ] _ Γ₁ ∘ [ α ∣ Γ₁ ]f ∘ [ ψ [ _ ∣ Γ ] I Γ₀ ⊗ id ∣ Γ₁ ]f ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] (αψ Γ₁ ∘ refl ∘ refl) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ α ∘ ψ ([ _ ∣ Γ ] ⊗ [ I ∣ Γ₀ ]) _ Γ₁ ∘ [ ψ [ _ ∣ Γ ] I Γ₀ ⊗ id ∣ Γ₁ ]f ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] ((ass ∙ (refl ∘ (~ nψ Γ₁ (ψ [ _ ∣ Γ ] I Γ₀))) ∙ ~ ass) ∘ refl) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ α ∘ ψ [ _ ∣ Γ ] _ Γ₀ ⊗ id ∘ ψ [ [ _ ∣ Γ ] ⊗ I ∣ Γ₀ ] _ Γ₁ ∘  [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ (refl ∘ [≐∣ Δ' ] (ass ∙ ass) ∙ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass)) ∙ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ α ∣ Δ' ]f ∘  [ ψ [ _ ∣ Γ ] I Γ₀ ⊗ id ∣ Δ' ]f ∘ [ ψ [ [ _ ∣ Γ ] ⊗ I ∣ Γ₀ ] _ Γ₁ ∘  [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ (~ (ψ++ _ _ Γ₀ (_ ∷ Δ'))) ∘ ([≐∣ Δ' ] (~ nψ Γ₁ [ ρ ∣ Γ₀ ]f) ∙ [∘∣ Δ' ] _ _) ∙ (~ ass) ⟩
      ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Δ') ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
    ≐⟨ refl ⟩
      φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
    qed≐
soundccut-j Δ₀ f (Il g) refl = soundccut-j Δ₀ f g refl
soundccut-j Δ₀ f (⊗l g) refl = soundccut-j (_ ∷ Δ₀) f g refl
soundccut-j {Γ = Γ₁} Δ₀ {Δ'} f (⊗c Γ Δ g) p with cases++ Δ₀ Γ Δ' (_ ∷ Δ) p
soundccut-j {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
  soundccut-j Δ₀ f g refl ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ ] _ _
            ∙ [≐∣ Δ ] (~ (refl ∘ refl ⊗ (~ f⊗id) ∙ nα-1))
            ∙ [∘∣ Δ ] _ _))
  ∙ ~ ass
soundccut-j {Γ = Γ₁} .Γ {.Δ} f (⊗c Γ Δ g) refl | inj₂ ([] , refl , refl) = soundlet⊗-j Γ Δ f g 
soundccut-j {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
  soundccut-j (Γ ++ _ ∷ _ ∷ Γ₀) f g refl ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ' ] _ _
            ∙ [≐∣ Δ' ] lem
            ∙ [∘∣ Δ' ] _ _))
  ∙ ~ ass
  where
    lem : id ⊗ sound f ∘ ψ _ _ Γ₁ ∘ [ [ α-1 ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f ≐
          [ α-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ ψ _ _ Γ₁)
    lem =
      proof≐
        id ⊗ sound f ∘ ψ _ _ Γ₁ ∘ [ [ α-1 ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f
      ≐⟨ ass ⟩ 
        id ⊗ sound f ∘ (ψ _ _ Γ₁ ∘ [ [ α-1 ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f)
      ≐⟨ refl ∘ (~ nψ Γ₁  [ α-1 ∣ Γ₀ ]f) ⟩ 
        id ⊗ sound f ∘ ([ α-1 ∣ Γ₀ ]f ⊗ id ∘ ψ _ _ Γ₁)
      ≐⟨ ~ ass ⟩ 
        id ⊗ sound f ∘ [ α-1 ∣ Γ₀ ]f ⊗ id ∘ ψ _ _ Γ₁
      ≐⟨ id⊗swap ∘ refl ⟩ 
        [ α-1 ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ ψ _ _ Γ₁
      ≐⟨ ass ⟩ 
        [ α-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ ψ _ _ Γ₁)
      qed≐

soundccut-n-true Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
soundccut-n-true {Γ = Γ} [] f (uf {Δ} g) refl = 
  proof≐
    sound (scut f g) ∘ [ [ l ∣ Γ ]f ∣ Δ ]f
  ≐⟨ soundscut Δ f g ∘ refl ⟩
    sound g ∘ [ sound f ∣ Δ ]f ∘ [ [ l ∣ Γ ]f ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ lψ Γ) ⟩
    sound g ∘ [ sound f ∣ Δ ]f ∘ [ l ∘ ψ I _ Γ ∣ Δ ]f
  ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _ ∙ [≐∣ Δ ] (~ ass))) ⟩
    sound g ∘ [ sound f ∘ l ∘ ψ I _ Γ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ nl ∘ refl ∙ ass) ⟩
    sound g ∘ [ l ∘ (id ⊗ sound f ∘ ψ I _ Γ) ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩
    sound g ∘ ([ l ∣ Δ ]f ∘ [ id ⊗ sound f ∘ ψ I _ Γ ∣ Δ ]f)
  ≐⟨ ~ ass ⟩
    sound g ∘ [ l ∣ Δ ]f ∘ [ id ⊗ sound f ∘ ψ I _ Γ ∣ Δ ]f
  qed≐
soundccut-n-true {Γ = Γ} (x ∷ Δ₀) {Δ'} f (uf g) refl =
  soundccut-n-true Δ₀ f g refl ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ' ] _ _
            ∙ [≐∣ Δ' ] (((ass ∙ (refl ∘ (~ nψ Γ [ l ∣ Δ₀ ]f)) ∙ ~ ass) ∙ (id⊗swap ∘ refl)) ∙ ass)
            ∙ [∘∣ Δ' ] _ _ ))
  ∙ ~ ass
soundccut-n-true Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
soundccut-n-true Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
soundccut-n-true {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
  proof≐
    sound (ccut true Δ₀ f g refl) ⊗ sound g' ∘ φ' _ Γ₀ Δ
  ≐⟨ soundccut-n-true Δ₀ f g refl ⊗ refl ∘ refl ⟩ 
    (sound g ∘ [ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f) ⊗ sound g' ∘ φ' _ Γ₀ Δ
  ≐⟨ refl ⊗ rid ∙ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ [ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ
  ≐⟨ refl ∘ refl ∙ ass ⟩ 
    sound g ⊗ sound g' ∘ ([ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ)
  ≐⟨ refl ∘ nφ' Γ₀ Δ (id ⊗ sound f ∘ ψ _ _ Γ) ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ ψ _ _ Γ ∣ Γ₀ ]f ∣ Δ ]f
  qed≐
soundccut-n-true {Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    sound g ⊗ sound (ccut true Γ₀ f g' refl) ∘ φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
  ≐⟨ refl ⊗ soundccut-n-true Γ₀ f g' refl ∘ refl ⟩ 
    sound g ⊗ (sound g' ∘ [ id ⊗ sound f ∘ ψ _ _ Γ₁ ∣ Δ' ]f) ∘ φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
  ≐⟨ rid ⊗ refl ∙ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∘ ψ _ _ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
  ≐⟨ refl ∘ (refl ⊗ [∘∣ Δ' ] _ _ ∙ (rid ⊗ refl ∙ f⊗∘)) ∙ ~ ass ∘ refl ∙ ass ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (id ⊗ [ ψ _ _ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ'))
  ≐⟨ refl ∘ lem ⟩
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f)
  ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩ 
    sound g ⊗ sound g' ∘ (id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ')) ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
  ≐⟨ refl ∘ nφ'2 Γ Γ₀ Δ' (sound f) ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∣ Δ' ]f) ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
  ≐⟨ ~ ass ∘ refl ∙ ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)  ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∘ ψ _ _ Γ₁ ∣ Δ' ]f
  qed≐
  where
  lem : id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘  φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
        ≐ φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
  lem =
    proof≐
      id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘  φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
    ≐⟨ ~ ass ⟩
      id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘ ψ _ I (Γ₀ ++ _ ∷ Γ₁ ++ Δ') ∘ [ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ ψ++ _ _ (Γ₀ ++ _ ∷ Γ₁) Δ' ∘ refl ⟩
      id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘ (ψ [ _ ∣ Γ ] [ I ∣ Γ₀ ++ _ ∷ Γ₁ ] Δ' ∘ [ ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Γ₁) ∣ Δ' ]f) ∘ [ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ (~ ass) ∘ refl ⟩
      (id ⊗ [ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘ ψ [ _ ∣ Γ ] [ I ∣ Γ₀ ++ _ ∷ Γ₁ ] Δ') ∘ [ ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Γ₁) ∣ Δ' ]f ∘ [ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ nψ2 Δ' (ψ [ I ∣ Γ₀ ] _ Γ₁) ∘ refl ∘ refl ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ id ⊗ ψ [ I ∣ Γ₀ ] _ Γ₁ ∣ Δ' ]f ∘ [ ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Γ₁) ∣ Δ' ]f ∘ [ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _) ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _) ∙ (refl ∘ [≐∣ Δ' ] (~ ass)) ) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ id ⊗ ψ [ I ∣ Γ₀ ] _ Γ₁ ∘ ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Γ₁) ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] (refl ∘ ψ++ _ _ Γ₀ (_ ∷ Γ₁) ∘ refl) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ id ⊗ ψ [ I ∣ Γ₀ ] _ Γ₁ ∘ (ψ [ _ ∣ Γ ] _ Γ₁ ∘ [ α ∣ Γ₁ ]f ∘ [ ψ [ _ ∣ Γ ] I Γ₀ ⊗ id ∣ Γ₁ ]f) ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] ((~ ass ∙ ((~ ass) ∘ refl)) ∘ refl) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ id ⊗ ψ [ I ∣ Γ₀ ] _ Γ₁ ∘ ψ [ _ ∣ Γ ] _ Γ₁ ∘ [ α ∣ Γ₁ ]f ∘ [ ψ [ _ ∣ Γ ] I Γ₀ ⊗ id ∣ Γ₁ ]f ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] (αψ Γ₁ ∘ refl ∘ refl) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ α ∘ ψ ([ _ ∣ Γ ] ⊗ [ I ∣ Γ₀ ]) _ Γ₁ ∘ [ ψ [ _ ∣ Γ ] I Γ₀ ⊗ id ∣ Γ₁ ]f ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] ((ass ∙ (refl ∘ (~ nψ Γ₁ (ψ [ _ ∣ Γ ] I Γ₀))) ∙ ~ ass) ∘ refl) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ α ∘ ψ [ _ ∣ Γ ] _ Γ₀ ⊗ id ∘ ψ [ [ _ ∣ Γ ] ⊗ I ∣ Γ₀ ] _ Γ₁ ∘  [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ (refl ∘ [≐∣ Δ' ] (ass ∙ ass) ∙ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass)) ∙ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass) ⟩
      ψ [ _ ∣ Γ ] _ Δ' ∘ [ α ∣ Δ' ]f ∘  [ ψ [ _ ∣ Γ ] I Γ₀ ⊗ id ∣ Δ' ]f ∘ [ ψ [ [ _ ∣ Γ ] ⊗ I ∣ Γ₀ ] _ Γ₁ ∘  [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ (~ (ψ++ _ _ Γ₀ (_ ∷ Δ'))) ∘ ([≐∣ Δ' ] (~ nψ Γ₁ [ ρ ∣ Γ₀ ]f) ∙ [∘∣ Δ' ] _ _) ∙ (~ ass) ⟩
      ψ [ _ ∣ Γ ] I (Γ₀ ++ _ ∷ Δ') ∘ [ [ ρ ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
    ≐⟨ refl ⟩
      φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ ψ _ _ Γ₁ ∣ Δ' ]f
    qed≐
soundccut-n-true Δ₀ f (Il g) refl = soundccut-n-true Δ₀ f g refl
soundccut-n-true Δ₀ f (⊗l g) refl = soundccut-n-true (_ ∷ Δ₀) f g refl
soundccut-n-true {Γ = Γ₁} Δ₀ {Δ'} f (⊗c Γ Δ g) p with cases++ Δ₀ Γ Δ' (_ ∷ Δ) p
soundccut-n-true {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
  soundccut-n-true Δ₀ f g refl ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ ] _ _
            ∙ [≐∣ Δ ] (~ (refl ∘ refl ⊗ (~ f⊗id) ∙ nα-1))
            ∙ [∘∣ Δ ] _ _))
  ∙ ~ ass
soundccut-n-true {Γ = Γ₁} .Γ {.Δ} f (⊗c Γ Δ g) refl | inj₂ ([] , refl , refl) = soundlet⊗-n-true Γ Δ f g 
soundccut-n-true {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
  soundccut-n-true (Γ ++ _ ∷ _ ∷ Γ₀) f g refl ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ' ] _ _
            ∙ [≐∣ Δ' ] lem
            ∙ [∘∣ Δ' ] _ _))
  ∙ ~ ass
  where
    lem : id ⊗ sound f ∘ ψ _ _ Γ₁ ∘ [ [ α-1 ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f ≐
          [ α-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ ψ _ _ Γ₁)
    lem =
      proof≐
        id ⊗ sound f ∘ ψ _ _ Γ₁ ∘ [ [ α-1 ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f
      ≐⟨ ass ⟩ 
        id ⊗ sound f ∘ (ψ _ _ Γ₁ ∘ [ [ α-1 ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f)
      ≐⟨ refl ∘ (~ nψ Γ₁  [ α-1 ∣ Γ₀ ]f) ⟩ 
        id ⊗ sound f ∘ ([ α-1 ∣ Γ₀ ]f ⊗ id ∘ ψ _ _ Γ₁)
      ≐⟨ ~ ass ⟩ 
        id ⊗ sound f ∘ [ α-1 ∣ Γ₀ ]f ⊗ id ∘ ψ _ _ Γ₁
      ≐⟨ id⊗swap ∘ refl ⟩ 
        [ α-1 ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ ψ _ _ Γ₁
      ≐⟨ ass ⟩ 
        [ α-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ ψ _ _ Γ₁)
      qed≐

soundlet⊗-n-false Δ₀ Δ₁ (uf {Γ}{A} f) g = 
  proof≐
    sound (let⊗ false Δ₀ Δ₁ f g)
  ≐⟨ soundlet⊗-j Δ₀ Δ₁ f g ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] A Γ ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ rid) ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ id) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ (refl ∘ (~ [id∣ Γ ]))) ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ [ id ∣ Γ ]f) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ (refl ∘ [≐∣ Γ ] lαρ)) ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ [ id ⊗ l ∘ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ (refl ∘ ([≐∣ Γ ] ass ∙ [∘∣ Γ ] _ _) ∙ ~ ass)) ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ [ id ⊗ l ∣ Γ ]f ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ ((~ nψ2 Γ l) ∘ refl)) ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (id ⊗ [ l ∣ Γ ]f ∘ ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ (~ ass ∘ refl) ∙ ass) ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ id ⊗ [ l ∣ Γ ]f ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] ((~ f⊗∘) ∘ refl) ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ (id ∘ id) ⊗ (sound f ∘ [ l ∣ Γ ]f) ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (lid ⊗ refl ∘ (refl ∘ [∘∣ Γ ] _ _ ∙ ~ ass)) ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ l ∣ Γ ]f) ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∣ Γ ]f ∘ [ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
  qed≐
soundlet⊗-n-false Δ₀ Δ₁ (⊗r {Γ = Γ}{Δ} f f') g =
  soundccut-n-false Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) f' g refl) refl
  ∙ (soundccut-n-false (Δ₀ ++ _ ∷ []) f' g refl ∘ refl)
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] lem ∙ [∘∣ Δ₁ ] _ _))
  ∙ ~ ass
  where
  lem : id ⊗ sound f' ∘ φ' _ (Δ₀ ++ _ ∷ []) Δ ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Δ ]f
        ≐ α-1 ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ φ' _ Δ₀ (Γ ++ Δ))
  lem =
    proof≐
      id ⊗ sound f' ∘ φ' _ (Δ₀ ++ _ ∷ []) Δ ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Δ ]f
    ≐⟨ ~ f⊗id ⊗ refl ∘ refl ∘ refl ⟩
      id ⊗ id ⊗ sound f' ∘ (ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ ρ ∣ Δ ]f) ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Δ ]f
    ≐⟨ ~ ass ∘ refl ∙ ass ⟩
      id ⊗ id ⊗ sound f' ∘ ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ ([ ρ ∣ Δ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (~ [∘∣ Δ ] _ _) ⟩
      id ⊗ id ⊗ sound f' ∘ ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ ρ ∘ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] nρ ⟩
      id ⊗ id ⊗ sound f' ∘ ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∘ ρ ∣ Δ ]f
    ≐⟨ refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass ∙ (ass ∘ refl)) ⟩
      id ⊗ id ⊗ sound f' ∘ (ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∣ Δ ]f) ∘ [ ρ ∣ Δ ]f
    ≐⟨ refl ∘ (~ nψ Δ (id ⊗ sound f ∘ φ' _ Δ₀ Γ)) ∘ refl ⟩
      id ⊗ id ⊗ sound f' ∘ ((id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∘ ψ [ _ ∣ Δ₀ ++ Γ ] I Δ) ∘ [ ρ ∣ Δ ]f
    ≐⟨ (~ ass) ∘ refl ∙ ass ⟩
      id ⊗ id ⊗ sound f' ∘ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
    ≐⟨ (refl ∘ (refl ⊗ rid ∙ f⊗∘) ∙ ~ ass) ∘ refl ⟩
      id ⊗ id ⊗ sound f' ∘ id ⊗ sound f ⊗ id ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
    ≐⟨ (~ f⊗∘ ∙ (f⊗id ∘ refl ∙ lid) ⊗ (~ rid)) ∘ refl  ∘ refl ⟩
      id ⊗ sound f ⊗ sound f' ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
    ≐⟨ ~ lid ∘ refl ∘ refl ⟩
      id ∘ id ⊗ sound f ⊗ sound f' ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
    ≐⟨ (~ α-1α) ∘ refl ∘ refl ∘ refl ⟩
      α-1 ∘ α ∘ id ⊗ sound f ⊗ sound f' ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
    ≐⟨ ass ∘ refl ∘ refl ⟩
      α-1 ∘ (α ∘ id ⊗ sound f ⊗ sound f') ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
    ≐⟨ refl ∘ nα ∘ refl ∘ refl ⟩
      α-1 ∘ (id ⊗ (sound f ⊗ sound f') ∘ α) ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
    ≐⟨ ((~ ass) ∘ refl ∙ ass) ∘ refl ∙ ass ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ)
    ≐⟨ refl ∘ (~ αφ' Δ₀ Γ Δ) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ φ' _ Γ Δ ∘ φ' _ Δ₀ (Γ ++ Δ))
    ≐⟨ ~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl) ∙ ass ⟩
      α-1 ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ φ' _ Δ₀ (Γ ++ Δ))
    qed≐
soundlet⊗-n-false Δ₀ Δ₁ (⊗c Γ Δ f) g = 
  proof≐
    sound (let⊗ false Δ₀ Δ₁ f g) ∘ [ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f
  ≐⟨ soundlet⊗-n-false Δ₀ Δ₁ f g ∘ refl ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f
  ≐⟨ ass ∘ refl ∙ ass ⟩ 
    sound g ∘ ([ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f)
  ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ sound f ∘ (φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ sound f ∘ (id ⊗ [ α-1 ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ)) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ (sound f ∘ [ α-1 ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
  ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
    sound g ∘ ([ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ α-1 ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ α-1 ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
  qed≐
  where
    lem :  φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f ≐ id ⊗ [ α-1 ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ)
    lem =
      proof≐
        φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f
      ≐⟨ φ'++ _ Δ₀ Γ (_ ∷ _ ∷ Δ) ∘ refl ⟩
        ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ α ⊗ id ∣ Δ ]f ∘ [ (φ' _ Δ₀ Γ ⊗ id) ⊗ id ∣ Δ ]f ∘ [ α-1 ∣ Δ ]f
      ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _ ∙ [≐∣ Δ ] (~ ass)))))) ) ⟩
        ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (φ' _ Δ₀ Γ ⊗ id ⊗ id ∘ α-1) ∣ Δ ]f
      ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ (~ nα-1)) ⟩
        ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (α-1 ∘ φ' _ Δ₀ Γ ⊗ (id ⊗ id)) ∣ Δ ]f
      ≐⟨ refl ∘ [≐∣ Δ ] (~ ass ∙ (refl ∘ refl ⊗ f⊗id)) ⟩
        ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ α-1 ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
      ≐⟨ refl ∘ [≐∣ Δ ] ((~ ααα-1) ∘ refl) ⟩
        ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ α-1 ∘ α ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
      ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ∙ ~ ass ⟩
        ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ α-1 ∣ Δ ]f ∘ [ α ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
      ≐⟨ (~ nψ2 Δ α-1) ∘ refl ⟩
        id ⊗ [ α-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _) Δ ∘ [ α ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
      ≐⟨ ass ∙ (refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass))) ⟩
        id ⊗ [ α-1 ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f)
      ≐⟨ refl ∘ (~ (φ'++ _ Δ₀ Γ (_ ∷ Δ))) ⟩
        id ⊗ [ α-1 ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ)
      qed≐



soundlet⊗-j Δ₀ Δ₁ ax g =
  rid ∙ (refl ∘ (~ [id∣ Δ₁ ] ∙ [≐∣ Δ₁ ] (rid ∙ (~ f⊗id ∘ refl))))
soundlet⊗-j Δ₀ Δ₁ (⊗r {Γ = Γ}{Δ} f f') g =
  soundccut-j Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) f' g refl) refl
  ∙ (soundccut-n-false (Δ₀ ++ _ ∷ []) f' g refl ∘ refl)
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] lem ∙ [∘∣ Δ₁ ] _ _))
  ∙ ~ ass
  where
  lem : id ⊗ sound f' ∘ φ' _ (Δ₀ ++ _ ∷ []) Δ ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f
        ≐ α-1 ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ))
  lem =
    proof≐
      id ⊗ sound f' ∘ φ' _ (Δ₀ ++ _ ∷ []) Δ ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f
    ≐⟨ ~ f⊗id ⊗ refl ∘ refl ∘ refl ⟩
      id ⊗ id ⊗ sound f' ∘ (ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ ρ ∣ Δ ]f) ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f
    ≐⟨ ~ ass ∘ refl ∙ ass ⟩
      id ⊗ id ⊗ sound f' ∘ ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ ([ ρ ∣ Δ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (~ [∘∣ Δ ] _ _) ⟩
      id ⊗ id ⊗ sound f' ∘ ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ ρ ∘ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] nρ ⟩
      id ⊗ id ⊗ sound f' ∘ ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ⊗ id ∘ ρ ∣ Δ ]f
    ≐⟨ refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass ∙ (ass ∘ refl)) ⟩
      id ⊗ id ⊗ sound f' ∘ (ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ⊗ id ∣ Δ ]f) ∘ [ ρ ∣ Δ ]f
    ≐⟨ refl ∘ (~ nψ Δ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ)) ∘ refl ⟩
      id ⊗ id ⊗ sound f' ∘ ((id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ⊗ id ∘ ψ [ _ ∣ Δ₀ ++ _ ∷ Γ ] I Δ) ∘ [ ρ ∣ Δ ]f
    ≐⟨ (~ ass) ∘ refl ∙ ass ⟩
      id ⊗ id ⊗ sound f' ∘ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ (refl ∘ (refl ⊗ rid ∙ f⊗∘) ∙ ~ ass) ∘ refl ⟩
      id ⊗ id ⊗ sound f' ∘ id ⊗ sound f ⊗ id ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ (~ f⊗∘ ∙ (f⊗id ∘ refl ∙ lid) ⊗ (~ rid)) ∘ refl  ∘ refl ⟩
      id ⊗ sound f ⊗ sound f' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ ~ lid ∘ refl ∘ refl ⟩
      id ∘ id ⊗ sound f ⊗ sound f' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ (~ α-1α) ∘ refl ∘ refl ∘ refl ⟩
      α-1 ∘ α ∘ id ⊗ sound f ⊗ sound f' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ ass ∘ refl ∘ refl ⟩
      α-1 ∘ (α ∘ id ⊗ sound f ⊗ sound f') ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ refl ∘ nα ∘ refl ∘ refl ⟩
      α-1 ∘ (id ⊗ (sound f ⊗ sound f') ∘ α) ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ ((~ ass) ∘ refl ∙ ass) ∘ refl ∙ ass ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ Γ Δ)
    ≐⟨ refl ∘ (~ ass ∙ (ass ∘ refl)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ ψ [ _ ∣ Γ ] _ Δ) ∘ [ ρ ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ nψ Δ (ψ [ _ ∣ Δ₀ ] _ Γ) ∘ refl) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ (ψ ([ _ ∣ Δ₀ ] ⊗ [ _ ∣ Γ ]) I Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f) ∘ [ ρ ∣ Δ ]f)
    ≐⟨ refl ∘ (~ ass ∘ refl) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ ψ ([ _ ∣ Δ₀ ] ⊗ [ _ ∣ Γ ]) I Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f)
    ≐⟨ refl ∘ ((~ αψ Δ) ∘ refl ∘ refl) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f)
    ≐⟨ refl ∘ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _)))) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ ρ) ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ [≐∣ Δ ] (refl ∘ ~ nρ)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∘ (ρ ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ [≐∣ Δ ] (~ ass)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∘ ρ ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ [≐∣ Δ ] (αρ ∘ refl)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ id ⊗ ρ ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ ((~ ass) ∙ (ass ∘ refl))) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ (ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ id ⊗ ρ ∣ Δ ]f) ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ (~ nψ2 Δ ρ) ∘ refl) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ (id ⊗ [ ρ ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ) ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (~ ass ∘ refl ∙ ass) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ id ⊗ [ ρ ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f))
    ≐⟨ refl ∘ ((~ f⊗∘ ∙ lid ⊗ refl) ∘ (~ ψ++ _ _ Γ Δ)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ (ψ [ _ ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ))
    ≐⟨ ~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl) ∙ ass ⟩
      α-1 ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ))
    qed≐
soundlet⊗-j Δ₀ Δ₁ (Il {Γ} f) g = soundlet⊗-n-true Δ₀ Δ₁ f g
soundlet⊗-j Δ₀ Δ₁ (⊗l {Γ} f) g = 
  soundlet⊗-j Δ₀ Δ₁ f g ∘ refl
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass ∘ refl ∙ ass) ∙ (refl ∘ (~ [∘∣ Γ ] _ _ ∙ [≐∣ Γ ] (αα-1) ∙ [id∣ Γ ]) ∙ ~ rid))))
soundlet⊗-j Δ₀ Δ₁ (⊗c Γ Δ f) g = 
  proof≐
    sound (let⊗ _ Δ₀ Δ₁ f g) ∘ [ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f
  ≐⟨ soundlet⊗-j Δ₀ Δ₁ f g ∘ refl ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f
  ≐⟨ ass ∘ refl ∙ ass ⟩ 
    sound g ∘ ([ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f)
  ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ sound f ∘ (id ⊗ [ α-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ (sound f ∘ [ α-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
  ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
    sound g ∘ ([ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ α-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ α-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
  qed≐
  where
    lem :  ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f ≐ id ⊗ [ α-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)
    lem =
      proof≐
        ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f
      ≐⟨ ψ++ _ _ Γ (_ ∷ _ ∷ Δ) ∘ refl ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ α ⊗ id ∣ Δ ]f ∘ [ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id) ⊗ id ∣ Δ ]f ∘ [ α-1 ∣ Δ ]f
      ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _ ∙ [≐∣ Δ ] (~ ass)))))) ) ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ⊗ id ∘ α-1) ∣ Δ ]f
      ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ (~ nα-1)) ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (α-1 ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ (id ⊗ id)) ∣ Δ ]f
      ≐⟨ refl ∘ [≐∣ Δ ] (~ ass ∙ (refl ∘ refl ⊗ f⊗id)) ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ α-1 ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
      ≐⟨ refl ∘ [≐∣ Δ ] ((~ ααα-1) ∘ refl) ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ α-1 ∘ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
      ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ∙ ~ ass ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ α-1 ∣ Δ ]f ∘ [ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
      ≐⟨ (~ nψ2 Δ (α-1)) ∘ refl ⟩
        id ⊗ [ α-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
      ≐⟨ ass ∙ (refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass))) ⟩
        id ⊗ [ α-1 ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f)
      ≐⟨ refl ∘ (~ (ψ++ _ _ Γ (_ ∷ Δ))) ⟩
        id ⊗ [ α-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)
      qed≐

soundlet⊗-n-true Δ₀ Δ₁ (uf {Γ} f) g =
  soundIc Δ₀ (Γ ++ Δ₁) (let⊗ true Δ₀ Δ₁ f g) refl
  ∙ (soundlet⊗-j Δ₀ Δ₁ f g ∘ refl)
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _
            ∙ [≐∣ Δ₁ ] lem))
  where
    lem : id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∘ [ id ⊗ l ∘ α ∣ Γ ]f
      ≐ id ⊗ (sound f ∘ [ l ∣ Γ ]f) ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ _) Γ ∘ [ α ∣ Γ ]f)
    lem =
      proof≐
        id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∘ [ id ⊗ l ∘ α ∣ Γ ]f
      ≐⟨ ass ⟩
        id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ∘ [ id ⊗ l ∘ α ∣ Γ ]f)
      ≐⟨ refl ∘ (refl ∘ [∘∣ Γ ] _ _) ⟩
        id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ∘ ([ id ⊗ l ∣ Γ ]f ∘ [ α ∣ Γ ]f))
      ≐⟨ refl ∘ (~ ass) ⟩
        id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ∘ [ id ⊗ l ∣ Γ ]f ∘ [ α ∣ Γ ]f)
      ≐⟨ refl ∘ ((~ nψ2 Γ l) ∘ refl) ⟩
        id ⊗ sound f ∘ (id ⊗ [ l ∣ Γ ]f ∘ ψ [ _ ∣ Δ₀ ] (I ⊗ _) Γ ∘ [ α ∣ Γ ]f)
      ≐⟨ ~ ass ∙ (~ ass ∘ refl) ∙ ass ⟩
        id ⊗ sound f ∘ id ⊗ [ l ∣ Γ ]f ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ _) Γ ∘ [ α ∣ Γ ]f)
      ≐⟨ (~ f⊗∘) ∘ refl ⟩
        (id ∘ id) ⊗ (sound f ∘ [ l ∣ Γ ]f) ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ _) Γ ∘ [ α ∣ Γ ]f)
      ≐⟨ lid ⊗ refl ∘ refl ⟩
        id ⊗ (sound f ∘ [ l ∣ Γ ]f) ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ _) Γ ∘ [ α ∣ Γ ]f)
      qed≐
soundlet⊗-n-true Δ₀ Δ₁ (⊗r {Γ = Γ}{Δ} f f') g =
  soundccut-n-true Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) f' g refl) refl
  ∙ (soundccut-n-false (Δ₀ ++ _ ∷ []) f' g refl ∘ refl)
  ∙ ass
  ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] lem ∙ [∘∣ Δ₁ ] _ _))
  ∙ ~ ass
  where
  lem : id ⊗ sound f' ∘ φ' _ (Δ₀ ++ _ ∷ []) Δ ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f
        ≐ α-1 ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ))
  lem =
    proof≐
      id ⊗ sound f' ∘ φ' _ (Δ₀ ++ _ ∷ []) Δ ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f
    ≐⟨ ~ f⊗id ⊗ refl ∘ refl ∘ refl ⟩
      id ⊗ id ⊗ sound f' ∘ (ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ ρ ∣ Δ ]f) ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f
    ≐⟨ ~ ass ∘ refl ∙ ass ⟩
      id ⊗ id ⊗ sound f' ∘ ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ ([ ρ ∣ Δ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (~ [∘∣ Δ ] _ _) ⟩
      id ⊗ id ⊗ sound f' ∘ ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ ρ ∘ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] nρ ⟩
      id ⊗ id ⊗ sound f' ∘ ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ⊗ id ∘ ρ ∣ Δ ]f
    ≐⟨ refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass ∙ (ass ∘ refl)) ⟩
      id ⊗ id ⊗ sound f' ∘ (ψ ([ _ ∣ Δ₀ ] ⊗ _) I Δ ∘ [ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ⊗ id ∣ Δ ]f) ∘ [ ρ ∣ Δ ]f
    ≐⟨ refl ∘ (~ nψ Δ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ)) ∘ refl ⟩
      id ⊗ id ⊗ sound f' ∘ ((id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ⊗ id ∘ ψ [ _ ∣ Δ₀ ++ _ ∷ Γ ] I Δ) ∘ [ ρ ∣ Δ ]f
    ≐⟨ (~ ass) ∘ refl ∙ ass ⟩
      id ⊗ id ⊗ sound f' ∘ (id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ (refl ∘ (refl ⊗ rid ∙ f⊗∘) ∙ ~ ass) ∘ refl ⟩
      id ⊗ id ⊗ sound f' ∘ id ⊗ sound f ⊗ id ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ (~ f⊗∘ ∙ (f⊗id ∘ refl ∙ lid) ⊗ (~ rid)) ∘ refl  ∘ refl ⟩
      id ⊗ sound f ⊗ sound f' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ ~ lid ∘ refl ∘ refl ⟩
      id ∘ id ⊗ sound f ⊗ sound f' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ (~ α-1α) ∘ refl ∘ refl ∘ refl ⟩
      α-1 ∘ α ∘ id ⊗ sound f ⊗ sound f' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ ass ∘ refl ∘ refl ⟩
      α-1 ∘ (α ∘ id ⊗ sound f ⊗ sound f') ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ refl ∘ nα ∘ refl ∘ refl ⟩
      α-1 ∘ (id ⊗ (sound f ⊗ sound f') ∘ α) ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
    ≐⟨ ((~ ass) ∘ refl ∙ ass) ∘ refl ∙ ass ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ Γ Δ)
    ≐⟨ refl ∘ (~ ass ∙ (ass ∘ refl)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ ψ [ _ ∣ Γ ] _ Δ) ∘ [ ρ ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ nψ Δ (ψ [ _ ∣ Δ₀ ] _ Γ) ∘ refl) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ (ψ ([ _ ∣ Δ₀ ] ⊗ [ _ ∣ Γ ]) I Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f) ∘ [ ρ ∣ Δ ]f)
    ≐⟨ refl ∘ (~ ass ∘ refl) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ ψ ([ _ ∣ Δ₀ ] ⊗ [ _ ∣ Γ ]) I Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f)
    ≐⟨ refl ∘ ((~ αψ Δ) ∘ refl ∘ refl) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f)
    ≐⟨ refl ∘ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _)))) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ ρ) ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ [≐∣ Δ ] (refl ∘ ~ nρ)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∘ (ρ ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ [≐∣ Δ ] (~ ass)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∘ ρ ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ [≐∣ Δ ] (αρ ∘ refl)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ id ⊗ ρ ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ ((~ ass) ∙ (ass ∘ refl))) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ (ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ id ⊗ ρ ∣ Δ ]f) ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (refl ∘ (~ nψ2 Δ ρ) ∘ refl) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ (id ⊗ [ ρ ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ) ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
    ≐⟨ refl ∘ (~ ass ∘ refl ∙ ass) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ id ⊗ [ ρ ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f))
    ≐⟨ refl ∘ ((~ f⊗∘ ∙ lid ⊗ refl) ∘ (~ ψ++ _ _ Γ Δ)) ⟩
      α-1 ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ (ψ [ _ ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ))
    ≐⟨ ~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl) ∙ ass ⟩
      α-1 ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ))
    qed≐
soundlet⊗-n-true Δ₀ Δ₁ (⊗c Γ Δ f) g = 
  proof≐
    sound (let⊗ _ Δ₀ Δ₁ f g) ∘ [ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f
  ≐⟨ soundlet⊗-n-true Δ₀ Δ₁ f g ∘ refl ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f
  ≐⟨ ass ∘ refl ∙ ass ⟩ 
    sound g ∘ ([ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f)
  ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ sound f ∘ (id ⊗ [ α-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)) ∣ Δ₁ ]f
  ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
    sound g ∘ [ α-1 ∘ id ⊗ (sound f ∘ [ α-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
  ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
    sound g ∘ ([ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ α-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ∘ [ α-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ α-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
  qed≐
  where
    lem :  ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f ≐ id ⊗ [ α-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)
    lem =
      proof≐
        ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ α-1 ∣ Δ ]f
      ≐⟨ ψ++ _ _ Γ (_ ∷ _ ∷ Δ) ∘ refl ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ α ⊗ id ∣ Δ ]f ∘ [ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id) ⊗ id ∣ Δ ]f ∘ [ α-1 ∣ Δ ]f
      ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _ ∙ [≐∣ Δ ] (~ ass)))))) ) ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ⊗ id ∘ α-1) ∣ Δ ]f
      ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ (~ nα-1)) ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (α-1 ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ (id ⊗ id)) ∣ Δ ]f
      ≐⟨ refl ∘ [≐∣ Δ ] (~ ass ∙ (refl ∘ refl ⊗ f⊗id)) ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ α-1 ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
      ≐⟨ refl ∘ [≐∣ Δ ] ((~ ααα-1) ∘ refl) ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ α-1 ∘ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
      ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ∙ ~ ass ⟩
        ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ α-1 ∣ Δ ]f ∘ [ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
      ≐⟨ (~ nψ2 Δ (α-1)) ∘ refl ⟩
        id ⊗ [ α-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
      ≐⟨ ass ∙ (refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass))) ⟩
        id ⊗ [ α-1 ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f)
      ≐⟨ refl ∘ (~ (ψ++ _ _ Γ (_ ∷ Δ))) ⟩
        id ⊗ [ α-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)
      qed≐

-- ====================================================================

-- sound ∘ cmplt is ≐-related to id

soundcmplt : {A B : Fma} (f : A ⇒ B)
  → sound (cmplt f) ≐ f
soundcmplt id = refl
soundcmplt (f ∘ g) = 
  soundscut [] (cmplt g) (cmplt f)
  ∙ (soundcmplt f ∘ soundcmplt g)
soundcmplt (f ⊗ g) =
  soundcmplt f ⊗ (soundcmplt g ∘ refl) ∘ refl
  ∙ (rid ⊗ refl ∙ f⊗∘ ∘ refl)
  ∙ ass
  ∙ (refl ∘ (refl ∘ (lid ∘ refl) ∙ (~ ass ∙ ~ lαρ)))
  ∙ ~ rid
soundcmplt l = lid
soundcmplt ρ = f⊗id ∘ refl ∙ (lid ∙ lid)
soundcmplt α =
  proof≐
    id ⊗ (id ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id) ∘ l ⊗ id) ∘ (id ∘ α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
  ≐⟨ refl ⊗ (~ ass ∙ (~ ass ∙ (~ rid ∙ refl ⊗ lid ∘ refl) ∘ refl) ∘ refl) ∘ (lid ∘ refl ∘ refl) ⟩
    id ⊗ (id ⊗ l ∘ α ∘ ρ ⊗ id ∘ l ⊗ id) ∘ (α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
  ≐⟨ refl ⊗ (~ lαρ ∘ refl ∙ lid) ∘ refl ⟩
    id ⊗ (l ⊗ id) ∘ (α ∘ α ⊗ id ∘ (ρ ⊗ id) ⊗ id)
  ≐⟨ ~ ass ∙ (~ ass ∘ refl) ⟩
    id ⊗ (l ⊗ id) ∘ α ∘ α ⊗ id ∘ (ρ ⊗ id) ⊗ id
  ≐⟨ ~ nα ∘ refl ∘ refl ⟩
    α ∘ (id ⊗ l) ⊗ id ∘ α ⊗ id ∘ (ρ ⊗ id) ⊗ id
  ≐⟨ ass ∙ (refl ∘ (~ f⊗∘ ∙ refl ⊗ lid) ∙ (ass ∙ (refl ∘ (~ f⊗∘ ∙ (~ ass) ⊗ lid)))) ⟩
    α ∘ (id ⊗ l ∘ α ∘ ρ ⊗ id) ⊗ id
  ≐⟨ refl ∘ (~ lαρ) ⊗ refl ∙ (refl ∘ f⊗id) ∙ ~ rid ⟩
    α
  qed≐
soundcmplt α-1 =
  proof≐
    (id ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id)) ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id) ∘ α-1
  ≐⟨ (~ ass ∙ (refl ⊗ lid ∘ lid ∘ refl)) ⊗ lid ∘ (ass ∙ lid) ∘ refl ⟩
    (id ⊗ l ∘ α ∘ ρ ⊗ id) ⊗ l ∘ (α ∘ ρ ⊗ id) ∘ α-1
  ≐⟨ ~ lαρ ⊗ refl ∘ refl ∘ refl ⟩
    id ⊗ l ∘ (α ∘ ρ ⊗ id) ∘ α-1
  ≐⟨ ~ ass ∘ refl ⟩
    id ⊗ l ∘ α ∘ ρ ⊗ id ∘ α-1
  ≐⟨ ~ lαρ ∘ refl ⟩
    id ∘ α-1
  ≐⟨ lid ⟩
    α-1
  qed≐

