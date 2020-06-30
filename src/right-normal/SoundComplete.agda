{-# OPTIONS --rewriting #-}

module SoundComplete where

open import Data.Empty
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
-- cut rules, letI, let⊗.

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


mutual
  soundletI : ∀{T Γ} Δ₀ Δ₁ {C}
    → (f : nothing ∣ Γ ⊢ I) (g : T ∣ Δ₀ ++ Δ₁ ⊢ C)
    → sound (letI Δ₀ Δ₁ f g) ≐ sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ T Δ₀ Γ ∣ Δ₁ ]f
  soundletI Δ₀ Δ₁ (uf {Γ}{A} f) g =
    proof≐
      sound (letI Δ₀ Δ₁ f g)
    ≐⟨ soundletI-j Δ₀ Δ₁ f g ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] A Γ ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ rid) ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ id) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ (refl ∘ (~ [id∣ Γ ]))) ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ [ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ (refl ∘ [≐∣ Γ ] lαρ)) ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ [ id ⊗ l ∘ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ (refl ∘ ([≐∣ Γ ] ass ∙ [∘∣ Γ ] _ _) ∙ ~ ass)) ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ [ id ⊗ l ∣ Γ ]f ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ ((~ nψ2 Γ l) ∘ refl)) ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (id ⊗ [ l ∣ Γ ]f ∘ ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ (~ ass ∘ refl) ∙ ass) ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ id ⊗ [ l ∣ Γ ]f ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ((~ f⊗∘) ∘ refl) ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ (id ∘ id) ⊗ (sound f ∘ [ l ∣ Γ ]f) ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (lid ⊗ refl ∘ (refl ∘ [∘∣ Γ ] _ _ ∙ ~ ass)) ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ l ∣ Γ ]f) ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∣ Γ ]f ∘ [ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    qed≐
  soundletI Δ₀ Δ₁ Ir g =
    rid
    ∙ (refl ∘ (~ [id∣ Δ₁ ] ∙ ([≐∣ Δ₁ ] (~ ρ-1ρ ∙ (refl ∘ (~ lid ∙ (~ f⊗id ∘ (~ lid))))) ∙ [∘∣ Δ₁ ] _ _)))
    ∙ ~ ass
  soundletI Δ₀ Δ₁ (Ic Γ Δ f) g = 
    proof≐
      sound (letI Δ₀ Δ₁ f g) ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ soundletI Δ₀ Δ₁ f g ∘ refl ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ Δ) ∣ Δ₁ ]f ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ ass ∘ refl ∙ ass ⟩ 
      sound g ∘ ([ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ Δ) ∣ Δ₁ ]f ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f)
    ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ (φ' _ Δ₀ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ (id ⊗ [ ρ-1 ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ)) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f
    ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
      sound g ∘ ([ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f
    qed≐
    where
      lem :  φ' _ Δ₀ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f ≐ id ⊗ [ ρ-1 ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ)
      lem =
        proof≐
          φ' _ Δ₀ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f
        ≐⟨ φ'++ _ Δ₀ Γ Δ ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ φ' _ Δ₀ Γ ∣ Δ ]f ∘ [ ρ-1 ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _)) ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ φ' _ Δ₀ Γ ∘ ρ-1 ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ nρ-1) ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ ρ-1 ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass) ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ ρ-1 ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ ρα-1) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ id ⊗ ρ-1 ∘ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass)) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ id ⊗ ρ-1 ∣ Δ ]f ∘ [ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (~ (nψ2 Δ ρ-1)) ∘ refl ∘ refl ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ I) Δ ∘ [ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ ass ∘ refl ∙ ass ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ I) Δ ∘ [ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f)
        ≐⟨ refl ∘ (~ (φ'++ _ Δ₀ Γ (I ∷ Δ))) ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ)
        qed≐
  soundletI Δ₀ Δ₁ (⊗c Γ Δ cJ cJ' f) g = 
    proof≐
      sound (letI Δ₀ Δ₁ f g) ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ soundletI Δ₀ Δ₁ f g ∘ refl ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ ass ∘ refl ∙ ass ⟩ 
      sound g ∘ ([ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f)
    ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ (φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ (id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ)) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
    ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
      sound g ∘ ([ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
    qed≐
    where
      lem :  φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f ≐ id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ)
      lem =
        proof≐
          φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f
        ≐⟨ φ'++ _ Δ₀ Γ (_ ∷ _ ∷ Δ) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ α ⊗ id ∣ Δ ]f ∘ [ (φ' _ Δ₀ Γ ⊗ id) ⊗ id ∣ Δ ]f ∘ [ αJ-1 cJ' ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _ ∙ [≐∣ Δ ] (~ ass)))))) ) ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (φ' _ Δ₀ Γ ⊗ id ⊗ id ∘ αJ-1 cJ') ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ (~ nαJ-1 cJ')) ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (αJ-1 cJ' ∘ φ' _ Δ₀ Γ ⊗ (id ⊗ id)) ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ ass ∙ (refl ∘ refl ⊗ f⊗id)) ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ αJ-1 cJ' ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] ((~ αααJ-1 cJ') ∘ refl) ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ αJ-1 cJ' ∘ α ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ∙ ~ ass ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ αJ-1 cJ' ∣ Δ ]f ∘ [ α ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (~ nψ2 Δ (αJ-1 cJ')) ∘ refl ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _) Δ ∘ [ α ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass))) ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f)
        ≐⟨ refl ∘ (~ (φ'++ _ Δ₀ Γ (_ ∷ Δ))) ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ)
        qed≐


  soundletI-j : ∀{T Γ} Δ₀ Δ₁ {A C}
    → (f : just A ∣ Γ ⊢ I) (g : T ∣ Δ₀ ++ Δ₁ ⊢ C)
    → sound (letI Δ₀ Δ₁ f g) ≐ sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ t T ∣ Δ₀ ] A Γ ∣ Δ₁ ]f
  soundletI-j Δ₀ Δ₁ ax g =
    rid ∙ (refl ∘ (~ [id∣ Δ₁ ] ∙ [≐∣ Δ₁ ] (rid ∙ (~ f⊗id ∘ refl))))
  soundletI-j {_}{Γ} Δ₀ Δ₁ (Il f) g =
    soundletI Δ₀ Δ₁ f g ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((ass ∙ (refl ∘ ass ∙ (~ ass ∙ (refl ∘ (~ [∘∣ Γ ] _ _ ∙ ([≐∣ Γ ] ρρ-1 ∙ [id∣ Γ ])))))) ∙ ~ rid)))
  soundletI-j {_}{Γ} Δ₀ Δ₁ (⊗l f) g =
    soundletI-j Δ₀ Δ₁ f g ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((ass ∙ (refl ∘ ass ∙ (~ ass ∙ (refl ∘ (~ [∘∣ Γ ] _ _ ∙ ([≐∣ Γ ] (ααJ-1 _) ∙ [id∣ Γ ])))))) ∙ ~ rid)))
  soundletI-j Δ₀ Δ₁ (Ic Γ Δ f) g =
    proof≐
      sound (letI Δ₀ Δ₁ f g) ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ soundletI-j Δ₀ Δ₁ f g ∘ refl ⟩
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∣ Δ₁ ]f ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ ass ∘ refl ∙ ass ⟩ 
      sound g ∘ ([ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∣ Δ₁ ]f ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f)
    ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ (id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ)) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f
    ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
      sound g ∘ ([ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f
    qed≐
      where
      lem :  ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f ≐ id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ)
      lem = 
        proof≐
          ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f
        ≐⟨ ψ++ _ _ Γ Δ ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f ∘ [ ρ-1 ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _)) ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∘ ρ-1 ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ nρ-1) ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ρ-1 ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass) ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ρ-1 ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ ρα-1) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ id ⊗ ρ-1 ∘ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass)) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ id ⊗ ρ-1 ∣ Δ ]f ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (~ (nψ2 Δ ρ-1)) ∘ refl ∘ refl ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ ass ∘ refl ∙ ass ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f)
        ≐⟨ refl ∘ (~ (ψ++ _ _ Γ (I ∷ Δ))) ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ)
        qed≐    
  soundletI-j Δ₀ Δ₁ (⊗c Γ Δ cJ cJ' f) g =
    proof≐
      sound (letI Δ₀ Δ₁ f g) ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ soundletI-j Δ₀ Δ₁ f g ∘ refl ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ ass ∘ refl ∙ ass ⟩ 
      sound g ∘ ([ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f)
    ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ sound f ∘ (id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
      sound g ∘ [ ρ-1 ∘ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
    ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
      sound g ∘ ([ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ ρ-1 ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
    qed≐
    where
      lem :  ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f ≐ id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)
      lem =
        proof≐
          ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f
        ≐⟨ ψ++ _ _ Γ (_ ∷ _ ∷ Δ) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ α ⊗ id ∣ Δ ]f ∘ [ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id) ⊗ id ∣ Δ ]f ∘ [ αJ-1 cJ' ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _ ∙ [≐∣ Δ ] (~ ass)))))) ) ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ⊗ id ∘ αJ-1 cJ') ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ (~ nαJ-1 cJ')) ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (αJ-1 cJ' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ (id ⊗ id)) ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ ass ∙ (refl ∘ refl ⊗ f⊗id)) ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ αJ-1 cJ' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] ((~ αααJ-1 cJ') ∘ refl) ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ αJ-1 cJ' ∘ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ∙ ~ ass ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ αJ-1 cJ' ∣ Δ ]f ∘ [ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (~ nψ2 Δ (αJ-1 cJ')) ∘ refl ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass))) ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f)
        ≐⟨ refl ∘ (~ (ψ++ _ _ Γ (_ ∷ Δ))) ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)
        qed≐



mutual
  soundscut : {S : Stp} → {Γ : Cxt} → (Δ' : Cxt) {A C : Fma} → 
       (f : S ∣ Γ ⊢ A) → (g : just A ∣ Δ' ⊢ C) → 
                 sound (scut f g) ≐ [scut] {S} {Γ} {Δ'} (sound g) (sound f)                 
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
      sound (scut f (ccut [] f' g refl))
    ≐⟨ soundscut (Δ' ++ Δ) f (ccut [] f' g refl) ⟩
      sound (ccut [] f' g refl) ∘ [ sound f ∣ Δ' ++ Δ ]f
    ≐⟨ soundccut [] f' g refl ∘ refl ⟩
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
  soundscut .(Γ ++ I ∷ Δ) Ir (Ic Γ Δ g) =
    soundscut (Γ ++ Δ) Ir g ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ ] _ _
              ∙ [≐∣ Δ ] (~ nρ-1)
              ∙ [∘∣ Δ ] _ _))
    ∙ ~ ass
  soundscut .(Γ ++ _ ⊗ _ ∷ Δ) Ir (⊗c Γ Δ cJ cJ' g) =
    soundscut (Γ ++ _ ∷ _ ∷ Δ) Ir g ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ ] _ _
              ∙ [≐∣ Δ ] (~ nαJ-1 _ ∙ (refl ∘ refl ⊗ f⊗id) )
              ∙ [∘∣ Δ ] _ _))
    ∙ ~ ass
  soundscut .(Γ ++ I ∷ Δ) (⊗r f f₁) (Ic Γ Δ g) =
    soundscut (Γ ++ Δ) (⊗r f f₁) g ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ ] _ _
              ∙ [≐∣ Δ ] (~ nρ-1)
              ∙ [∘∣ Δ ] _ _))
    ∙ ~ ass
  soundscut .(Γ ++ _ ⊗ _ ∷ Δ) (⊗r f f₁) (⊗c Γ Δ cJ cJ' g) = 
    soundscut (Γ ++ _ ∷ _ ∷ Δ) (⊗r f f₁) g ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ ] _ _
              ∙ [≐∣ Δ ] (~ nαJ-1 _ ∙ (refl ∘ refl ⊗ f⊗id) )
              ∙ [∘∣ Δ ] _ _))
    ∙ ~ ass
  soundscut Δ' (Ic Γ Δ f) g =
    soundscut Δ' f g ∘ refl
    ∙ ass
    ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)
  soundscut Δ' (⊗c Γ Δ cJ cJ' f) g = 
    soundscut Δ' f g ∘ refl
    ∙ ass
    ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)

  soundccut : {T : Stp} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma}  → 
       (f : nothing ∣ Γ ⊢ A) → (g : T ∣ Δ ⊢ C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
              sound (ccut Δ₀ f g p) ≐ [ccut] {T} {Γ} Δ₀ (sound g) (sound f) p
  soundccut Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
  soundccut Δ₀ f (uf g) p with  cases∷ Δ₀ p
  soundccut {Γ = Γ} .[] f (uf {Γ = Δ} g) refl | inj₁ (refl , refl , refl) =
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
  soundccut {Γ = Γ} .(_ ∷ Γ₀) {Δ'} f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
    proof≐
      sound (ccut Γ₀ f g refl) ∘ [ [ [ l ∣ Γ₀ ]f ∣ Γ ]f ∣ Δ' ]f
    ≐⟨ soundccut Γ₀ f g refl ∘ refl ⟩ 
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
  soundccut Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
  soundccut Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
  soundccut {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
    proof≐
      sound (ccut Δ₀ f g refl) ⊗ sound g' ∘ φ' _ Γ₀ Δ
    ≐⟨ soundccut Δ₀ f g refl ⊗ refl ∘ refl ⟩ 
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
  soundccut {Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
    proof≐
      sound g ⊗ sound (ccut Γ₀ f g' refl) ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
    ≐⟨ refl ⊗ soundccut Γ₀ f g' refl ∘ refl ⟩ 
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
  soundccut Δ₀ f (Il g) refl = soundccut Δ₀ f g refl
  soundccut Δ₀ f (⊗l g) refl = soundccut (_ ∷ Δ₀) f g refl
  soundccut Δ₀ {Δ'} f (Ic Γ Δ g) p with cases++ Δ₀ Γ Δ' (I ∷ Δ) p
  soundccut Δ₀ {.(Γ₀ ++ I ∷ Δ)} f (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
    soundccut Δ₀ f g refl ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ ] _ _
              ∙ [≐∣ Δ ] (~ nρ-1)
              ∙ [∘∣ Δ ] _ _))
    ∙ ~ ass
  soundccut .Γ {.Δ} f (Ic Γ Δ g) refl | inj₂ ([] , refl , refl) = soundletI Γ Δ f g
  soundccut {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} f (Ic Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.I ∷ Γ₀ , refl , refl) =
    soundccut (Γ ++ Γ₀) f g refl ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ' ] _ _
              ∙ [≐∣ Δ' ] lem
              ∙ [∘∣ Δ' ] _ _))
    ∙ ~ ass
    where
      lem : id ⊗ sound f ∘ φ' _ (Γ ++ Γ₀) Γ₁ ∘ [ [ ρ-1 ∣ Γ₀ ]f ∣ Γ₁ ]f ≐
            [ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ (Γ ++ I ∷ Γ₀) Γ₁)
      lem =
        proof≐
          id ⊗ sound f ∘ φ' _ (Γ ++ Γ₀) Γ₁ ∘ [ [ ρ-1 ∣ Γ₀ ]f ∣ Γ₁ ]f
        ≐⟨ ass ⟩ 
          id ⊗ sound f ∘ (φ' _ (Γ ++ Γ₀) Γ₁ ∘ [ [ ρ-1 ∣ Γ₀ ]f ∣ Γ₁ ]f)
        ≐⟨ refl ∘ (~ (nφ' Γ₀ Γ₁ ρ-1)) ⟩ 
          id ⊗ sound f ∘ ([ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ φ' _ (Γ ++ I ∷ Γ₀) Γ₁)
        ≐⟨ ~ ass ⟩ 
          id ⊗ sound f ∘ [ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ φ' _ (Γ ++ I ∷ Γ₀) Γ₁
        ≐⟨ id⊗swap ∘ refl ⟩ 
          [ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ φ' _ (Γ ++ I ∷ Γ₀) Γ₁
        ≐⟨ ass ⟩ 
          [ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ (Γ ++ I ∷ Γ₀) Γ₁)
        qed≐
  soundccut {Γ = Γ₁} Δ₀ {Δ'} f (⊗c Γ Δ cJ cJ' g) p with cases++ Δ₀ Γ Δ' (_ ∷ Δ) p
  soundccut {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ cJ cJ' g) refl | inj₁ (Γ₀ , refl , refl) =
    soundccut Δ₀ f g refl ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ ] _ _
              ∙ [≐∣ Δ ] (~ (refl ∘ refl ⊗ (~ f⊗id) ∙ nαJ-1 _))
              ∙ [∘∣ Δ ] _ _))
    ∙ ~ ass
  soundccut {Γ = Γ₁} .Γ {.Δ} f (⊗c Γ Δ cJ cJ' g) refl | inj₂ ([] , refl , refl) = soundlet⊗ Γ Δ f g
  soundccut {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') cJ cJ' g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    soundccut (Γ ++ _ ∷ _ ∷ Γ₀) f g refl ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ' ] _ _
              ∙ [≐∣ Δ' ] lem
              ∙ [∘∣ Δ' ] _ _))
    ∙ ~ ass
    where
      lem : id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ _ ∷ Γ₀) Γ₁ ∘ [ [ αJ-1 _ ∣ Γ₀ ]f ∣ Γ₁ ]f ≐
            [ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁)
      lem =
        proof≐
          id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ _ ∷ Γ₀) Γ₁ ∘ [ [ αJ-1 _ ∣ Γ₀ ]f ∣ Γ₁ ]f
        ≐⟨ ass ⟩ 
          id ⊗ sound f ∘ (φ' _ (Γ ++ _ ∷ _ ∷ Γ₀) Γ₁ ∘ [ [ αJ-1 _ ∣ Γ₀ ]f ∣ Γ₁ ]f)
        ≐⟨ refl ∘ (~ (nφ' Γ₀ Γ₁ (αJ-1 _))) ⟩ 
          id ⊗ sound f ∘ ([ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁)
        ≐⟨ ~ ass ⟩ 
          id ⊗ sound f ∘ [ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁
        ≐⟨ id⊗swap ∘ refl ⟩ 
          [ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁
        ≐⟨ ass ⟩ 
          [ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ Γ₀) Γ₁)
        qed≐

  soundccut-j : {T : Stp} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' C : Fma}  → 
       (f : just A' ∣ Γ ⊢ A) → (g : T ∣ Δ ⊢ C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
              sound (ccut Δ₀ f g p) ≐ [ccut]-j {T} {Γ} Δ₀ (sound g) (sound f) p
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
      sound (ccut Δ₀ f g refl) ⊗ sound g' ∘ φ' _ Γ₀ Δ
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
      sound g ⊗ sound (ccut Γ₀ f g' refl) ∘ φ' _ Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')
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
  soundccut-j Δ₀ {Δ'} f (Ic Γ Δ g) p with cases++ Δ₀ Γ Δ' (I ∷ Δ) p
  soundccut-j Δ₀ {.(Γ₀ ++ I ∷ Δ)} f (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
    soundccut-j Δ₀ f g refl ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ ] _ _
              ∙ [≐∣ Δ ] (~ nρ-1)
              ∙ [∘∣ Δ ] _ _))
    ∙ ~ ass
  soundccut-j .Γ {.Δ} f (Ic Γ Δ g) refl | inj₂ ([] , refl , refl) = soundletI-j Γ Δ f g
  soundccut-j {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} f (Ic Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.I ∷ Γ₀ , refl , refl) =
    soundccut-j (Γ ++ Γ₀) f g refl ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ' ] _ _
              ∙ [≐∣ Δ' ] lem
              ∙ [∘∣ Δ' ] _ _))
    ∙ ~ ass
    where
      lem : id ⊗ sound f ∘ ψ _ _ Γ₁ ∘ [ [ ρ-1 ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f ≐
            [ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ ψ _ _ Γ₁)
      lem =
        proof≐
          id ⊗ sound f ∘ ψ _ _ Γ₁ ∘ [ [ ρ-1 ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f
        ≐⟨ ass ⟩ 
          id ⊗ sound f ∘ (ψ _ _ Γ₁ ∘ [ [ ρ-1 ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f)
        ≐⟨ refl ∘ (~ nψ Γ₁ [ ρ-1 ∣ Γ₀ ]f) ⟩ 
          id ⊗ sound f ∘ ([ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ ψ _ _ Γ₁)
        ≐⟨ ~ ass ⟩ 
          id ⊗ sound f ∘ [ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ ψ _ _ Γ₁
        ≐⟨ id⊗swap ∘ refl ⟩ 
          [ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ ψ _ _ Γ₁
        ≐⟨ ass ⟩ 
          [ ρ-1 ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ ψ _ _ Γ₁)
        qed≐
  soundccut-j {Γ = Γ₁} Δ₀ {Δ'} f (⊗c Γ Δ cJ cJ' g) p with cases++ Δ₀ Γ Δ' (_ ∷ Δ) p
  soundccut-j {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ cJ cJ' g) refl | inj₁ (Γ₀ , refl , refl) =
    soundccut-j Δ₀ f g refl ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ ] _ _
              ∙ [≐∣ Δ ] (~ (refl ∘ refl ⊗ (~ f⊗id) ∙ nαJ-1 _))
              ∙ [∘∣ Δ ] _ _))
    ∙ ~ ass
  soundccut-j {Γ = Γ₁} .Γ {.Δ} f (⊗c Γ Δ cJ cJ' g) refl | inj₂ ([] , refl , refl) = soundlet⊗-j Γ Δ f g
  soundccut-j {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') cJ cJ' g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    soundccut-j (Γ ++ _ ∷ _ ∷ Γ₀) f g refl ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ' ] _ _
              ∙ [≐∣ Δ' ] lem
              ∙ [∘∣ Δ' ] _ _))
    ∙ ~ ass
    where
      lem : id ⊗ sound f ∘ ψ _ _ Γ₁ ∘ [ [ αJ-1 _ ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f ≐
            [ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ ψ _ _ Γ₁)
      lem =
        proof≐
          id ⊗ sound f ∘ ψ _ _ Γ₁ ∘ [ [ αJ-1 _ ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f
        ≐⟨ ass ⟩ 
          id ⊗ sound f ∘ (ψ _ _ Γ₁ ∘ [ [ αJ-1 _ ∣ Γ₀ ]f ∣ _ ∷ Γ₁ ]f)
        ≐⟨ refl ∘ (~ nψ Γ₁  [ αJ-1 cJ' ∣ Γ₀ ]f) ⟩ 
          id ⊗ sound f ∘ ([ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ ψ _ _ Γ₁)
        ≐⟨ ~ ass ⟩ 
          id ⊗ sound f ∘ [ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ ψ _ _ Γ₁
        ≐⟨ id⊗swap ∘ refl ⟩ 
          [ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ ψ _ _ Γ₁
        ≐⟨ ass ⟩ 
          [ αJ-1 _ ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ ψ _ _ Γ₁)
        qed≐


  soundlet⊗ : ∀{T Γ} Δ₀ Δ₁ {C J J' cJ cJ'}
    → (f : nothing ∣ Γ ⊢ J ⊗ J') (g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
    → sound (let⊗ Δ₀ Δ₁ cJ cJ' f g) ≐ sound g ∘ [ αJ-1 cJ' ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ T Δ₀ Γ ∣ Δ₁ ]f
  soundlet⊗ Δ₀ Δ₁ (uf {Γ}{A} f) g = 
    proof≐
      sound (let⊗ Δ₀ Δ₁ _ _ f g)
    ≐⟨ soundlet⊗-j Δ₀ Δ₁ f g ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] A Γ ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ rid) ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ id) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ (refl ∘ (~ [id∣ Γ ]))) ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ [ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ (refl ∘ [≐∣ Γ ] lαρ)) ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ [ id ⊗ l ∘ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ (refl ∘ ([≐∣ Γ ] ass ∙ [∘∣ Γ ] _ _) ∙ ~ ass)) ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] A Γ ∘ [ id ⊗ l ∣ Γ ]f ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ ((~ nψ2 Γ l) ∘ refl)) ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ (id ⊗ [ l ∣ Γ ]f ∘ ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ (~ ass ∘ refl) ∙ ass) ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ id ⊗ [ l ∣ Γ ]f ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ((~ f⊗∘) ∘ refl) ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ (id ∘ id) ⊗ (sound f ∘ [ l ∣ Γ ]f) ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∘ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (lid ⊗ refl ∘ (refl ∘ [∘∣ Γ ] _ _ ∙ ~ ass)) ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ l ∣ Γ ]f) ∘ (ψ [ _ ∣ Δ₀ ] (I ⊗ A) Γ ∘ [ α ∣ Γ ]f ∘ [ ρ ⊗ id ∣ Γ ]f) ∣ Δ₁ ]f
    qed≐
  soundlet⊗ Δ₀ Δ₁ (⊗r {Γ = Γ}{Δ} f f') g =
    soundccut Δ₀ f (ccut (Δ₀ ++ _ ∷ []) f' g refl) refl
    ∙ (soundccut (Δ₀ ++ _ ∷ []) f' g refl ∘ refl)
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] lem ∙ [∘∣ Δ₁ ] _ _))
    ∙ ~ ass
    where
    lem : id ⊗ sound f' ∘ φ' _ (Δ₀ ++ _ ∷ []) Δ ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Δ ]f
          ≐ αJ-1 _ ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ φ' _ Δ₀ (Γ ++ Δ))
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
      ≐⟨ (~ αJ-1α _) ∘ refl ∘ refl ∘ refl ⟩
        αJ-1 _ ∘ α ∘ id ⊗ sound f ⊗ sound f' ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
      ≐⟨ ass ∘ refl ∘ refl ⟩
        αJ-1 _ ∘ (α ∘ id ⊗ sound f ⊗ sound f') ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
      ≐⟨ refl ∘ nα ∘ refl ∘ refl ⟩
        αJ-1 _ ∘ (id ⊗ (sound f ⊗ sound f') ∘ α) ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ
      ≐⟨ ((~ ass) ∘ refl ∙ ass) ∘ refl ∙ ass ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ φ' _ Δ₀ Γ ⊗ id ∘ φ' [ _ ∣ Δ₀ ] Γ Δ)
      ≐⟨ refl ∘ (~ αφ' Δ₀ Γ Δ) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ φ' _ Γ Δ ∘ φ' _ Δ₀ (Γ ++ Δ))
      ≐⟨ ~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl) ∙ ass ⟩
        αJ-1 _ ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ φ' _ Δ₀ (Γ ++ Δ))
      qed≐
  soundlet⊗ Δ₀ Δ₁ (Ic Γ Δ f) g =
    proof≐
      sound (let⊗ Δ₀ Δ₁ _ _ f g) ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ soundlet⊗ Δ₀ Δ₁ f g ∘ refl ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ Δ) ∣ Δ₁ ]f ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ ass ∘ refl ∙ ass ⟩ 
      sound g ∘ ([ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ Δ) ∣ Δ₁ ]f ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f)
    ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ (φ' _ Δ₀ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ (id ⊗ [ ρ-1 ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ)) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f
    ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
      sound g ∘ ([ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f
    qed≐
    where
      lem :  φ' _ Δ₀ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f ≐ id ⊗ [ ρ-1 ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ)
      lem =
        proof≐
          φ' _ Δ₀ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f
        ≐⟨ φ'++ _ Δ₀ Γ Δ ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ φ' _ Δ₀ Γ ∣ Δ ]f ∘ [ ρ-1 ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _)) ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ φ' _ Δ₀ Γ ∘ ρ-1 ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ nρ-1) ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ ρ-1 ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass) ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ ρ-1 ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ ρα-1) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ id ⊗ ρ-1 ∘ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass)) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ I ∣ Γ ] Δ ∘ [ id ⊗ ρ-1 ∣ Δ ]f ∘ [ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (~ (nψ2 Δ ρ-1)) ∘ refl ∘ refl ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ I) Δ ∘ [ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ ass ∘ refl ∙ ass ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ I) Δ ∘ [ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f)
        ≐⟨ refl ∘ (~ (φ'++ _ Δ₀ Γ (I ∷ Δ))) ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ I ∷ Δ)
        qed≐
  soundlet⊗ Δ₀ Δ₁ (⊗c Γ Δ cJ cJ' f) g = 
    proof≐
      sound (let⊗ Δ₀ Δ₁ _ _ f g) ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ soundlet⊗ Δ₀ Δ₁ f g ∘ refl ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ ass ∘ refl ∙ ass ⟩ 
      sound g ∘ ([ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f)
    ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ (φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ (id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ)) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
    ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
      sound g ∘ ([ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
    qed≐
    where
      lem :  φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f ≐ id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ)
      lem =
        proof≐
          φ' _ Δ₀ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f
        ≐⟨ φ'++ _ Δ₀ Γ (_ ∷ _ ∷ Δ) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ α ⊗ id ∣ Δ ]f ∘ [ (φ' _ Δ₀ Γ ⊗ id) ⊗ id ∣ Δ ]f ∘ [ αJ-1 cJ' ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _ ∙ [≐∣ Δ ] (~ ass)))))) ) ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (φ' _ Δ₀ Γ ⊗ id ⊗ id ∘ αJ-1 cJ') ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ (~ nαJ-1 cJ')) ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (αJ-1 cJ' ∘ φ' _ Δ₀ Γ ⊗ (id ⊗ id)) ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ ass ∙ (refl ∘ refl ⊗ f⊗id)) ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ αJ-1 cJ' ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] ((~ αααJ-1 cJ') ∘ refl) ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ αJ-1 cJ' ∘ α ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ∙ ~ ass ⟩
          ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ αJ-1 cJ' ∣ Δ ]f ∘ [ α ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (~ nψ2 Δ (αJ-1 cJ')) ∘ refl ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _) Δ ∘ [ α ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass))) ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ I ∣ Γ ] ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f)
        ≐⟨ refl ∘ (~ (φ'++ _ Δ₀ Γ (_ ∷ Δ))) ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ φ' _ Δ₀ (Γ ++ _ ∷ Δ)
        qed≐

  soundlet⊗-j : ∀{T Γ} Δ₀ Δ₁ {A C J J' cJ cJ'}
    → (f : just A ∣ Γ ⊢ J ⊗ J') (g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
    → sound (let⊗ Δ₀ Δ₁ cJ cJ' f g) ≐ sound g ∘ [ αJ-1 cJ' ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ t T ∣ Δ₀ ] A Γ ∣ Δ₁ ]f
  soundlet⊗-j Δ₀ Δ₁ ax g =
    rid ∙ (refl ∘ (~ [id∣ Δ₁ ] ∙ [≐∣ Δ₁ ] (rid ∙ (~ f⊗id ∘ refl))))
  soundlet⊗-j Δ₀ Δ₁ {cJ' = cJ'} (⊗r {Γ = Γ}{Δ} f f') g =
    soundccut-j Δ₀ f (ccut (Δ₀ ++ _ ∷ []) f' g refl) refl
    ∙ (soundccut (Δ₀ ++ _ ∷ []) f' g refl ∘ refl)
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] lem ∙ [∘∣ Δ₁ ] _ _))
    ∙ ~ ass
    where
    lem : id ⊗ sound f' ∘ φ' _ (Δ₀ ++ _ ∷ []) Δ ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f
          ≐ αJ-1 _ ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ))
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
      ≐⟨ (~ αJ-1α cJ') ∘ refl ∘ refl ∘ refl ⟩
        αJ-1 _ ∘ α ∘ id ⊗ sound f ⊗ sound f' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
      ≐⟨ ass ∘ refl ∘ refl ⟩
        αJ-1 _ ∘ (α ∘ id ⊗ sound f ⊗ sound f') ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
      ≐⟨ refl ∘ nα ∘ refl ∘ refl ⟩
        αJ-1 _ ∘ (id ⊗ (sound f ⊗ sound f') ∘ α) ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ (_ ∷ Γ) Δ
      ≐⟨ ((~ ass) ∘ refl ∙ ass) ∘ refl ∙ ass ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ φ' _ Γ Δ)
      ≐⟨ refl ∘ (~ ass ∙ (ass ∘ refl)) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ ψ [ _ ∣ Γ ] _ Δ) ∘ [ ρ ∣ Δ ]f)
      ≐⟨ refl ∘ (refl ∘ nψ Δ (ψ [ _ ∣ Δ₀ ] _ Γ) ∘ refl) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ (ψ ([ _ ∣ Δ₀ ] ⊗ [ _ ∣ Γ ]) I Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f) ∘ [ ρ ∣ Δ ]f)
      ≐⟨ refl ∘ (~ ass ∘ refl) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (α ∘ ψ ([ _ ∣ Δ₀ ] ⊗ [ _ ∣ Γ ]) I Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f)
      ≐⟨ refl ∘ ((~ αψ Δ) ∘ refl ∘ refl) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f)
      ≐⟨ refl ∘ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _)))) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∘ ρ) ∣ Δ ]f)
      ≐⟨ refl ∘ (refl ∘ [≐∣ Δ ] (refl ∘ ~ nρ)) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∘ (ρ ∘ ψ [ _ ∣ Δ₀ ] _ Γ) ∣ Δ ]f)
      ≐⟨ refl ∘ (refl ∘ [≐∣ Δ ] (~ ass)) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ α ∘ ρ ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
      ≐⟨ refl ∘ (refl ∘ [≐∣ Δ ] (αρ ∘ refl)) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ id ⊗ ρ ∘ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
      ≐⟨ refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ ((~ ass) ∙ (ass ∘ refl))) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ (ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ I) Δ ∘ [ id ⊗ ρ ∣ Δ ]f) ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
      ≐⟨ refl ∘ (refl ∘ (~ nψ2 Δ ρ) ∘ refl) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ (id ⊗ [ ρ ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ) ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f)
      ≐⟨ refl ∘ (~ ass ∘ refl ∙ ass) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ ψ [ _ ∣ Γ ] I Δ ∘ id ⊗ [ ρ ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f))
      ≐⟨ refl ∘ ((~ f⊗∘ ∙ lid ⊗ refl) ∘ (~ ψ++ _ _ Γ Δ)) ⟩
        αJ-1 _ ∘ id ⊗ (sound f ⊗ sound f') ∘ (id ⊗ (ψ [ _ ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ))
      ≐⟨ ~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl) ∙ ass ⟩
        αJ-1 _ ∘ (id ⊗ (sound f ⊗ sound f' ∘ φ' _ Γ Δ) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ))
      qed≐

  soundlet⊗-j Δ₀ Δ₁ (Il {Γ} f) g =
    soundlet⊗ Δ₀ Δ₁ f g ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass ∘ refl ∙ ass) ∙ (refl ∘ (~ [∘∣ Γ ] _ _ ∙ [≐∣ Γ ] ρρ-1 ∙ [id∣ Γ ]) ∙ ~ rid))))
  soundlet⊗-j Δ₀ Δ₁ (⊗l {Γ} f) g = 
    soundlet⊗-j Δ₀ Δ₁ f g ∘ refl
    ∙ ass
    ∙ (refl ∘ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass ∘ refl ∙ ass) ∙ (refl ∘ (~ [∘∣ Γ ] _ _ ∙ [≐∣ Γ ] (ααJ-1 _) ∙ [id∣ Γ ]) ∙ ~ rid))))
  soundlet⊗-j Δ₀ Δ₁ (Ic Γ Δ f) g =
    proof≐
      sound (let⊗ Δ₀ Δ₁ _ _ f g) ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ soundlet⊗-j Δ₀ Δ₁ f g ∘ refl ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∣ Δ₁ ]f ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ ass ∘ refl ∙ ass ⟩ 
      sound g ∘ ([ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∣ Δ₁ ]f ∘ [ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f)
    ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ (id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ)) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f
    ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
      sound g ∘ ([ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ ρ-1 ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ) ∣ Δ₁ ]f
    qed≐
    where
      lem :  ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f ≐ id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ I ∷ Δ)
      lem =
        proof≐
          ψ [ _ ∣ Δ₀ ] _ (Γ ++ Δ) ∘ [ ρ-1 ∣ Δ ]f
        ≐⟨ ψ++ _ _ Γ Δ ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∣ Δ ]f ∘ [ ρ-1 ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _)) ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ∘ ρ-1 ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ nρ-1) ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ρ-1 ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass) ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ ρ-1 ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ ρα-1) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ id ⊗ ρ-1 ∘ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass)) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] [ _ ∣ Γ ] Δ ∘ [ id ⊗ ρ-1 ∣ Δ ]f ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (~ (nψ2 Δ ρ-1)) ∘ refl ∘ refl ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ ass ∘ refl ∙ ass ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f)
        ≐⟨ refl ∘ (~ (ψ++ _ _ Γ (_ ∷ Δ))) ⟩
          id ⊗ [ ρ-1 ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)
        qed≐
  soundlet⊗-j Δ₀ Δ₁ (⊗c Γ Δ cJ cJ' f) g = 
    proof≐
      sound (let⊗ Δ₀ Δ₁ _ _ f g) ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ soundlet⊗-j Δ₀ Δ₁ f g ∘ refl ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ ass ∘ refl ∙ ass ⟩ 
      sound g ∘ ([ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∣ Δ₁ ]f ∘ [ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f)
    ≐⟨ refl ∘ ((~ [∘∣ Δ₁ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₁ ] _ _ ∙ [≐∣ Δ₁ ] ((~ ass) ∘ refl))) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] ass ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ (ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (refl ∘ lem) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ sound f ∘ (id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)) ∣ Δ₁ ]f
    ≐⟨ refl ∘ [≐∣ Δ₁ ] (~ ass ∙ ((ass ∙ (refl ∘ (~ f⊗∘ ∙ lid ⊗ refl))) ∘ refl)) ⟩ 
      sound g ∘ [ αJ-1 _ ∘ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
    ≐⟨ refl ∘ ([≐∣ Δ₁ ] ass ∙ [∘∣ Δ₁ ] _ _) ⟩ 
      sound g ∘ ([ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ αJ-1 _ ∣ Δ₁ ]f ∘ [ id ⊗ (sound f ∘ [ αJ-1 cJ' ∣ Δ ]f) ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ) ∣ Δ₁ ]f
    qed≐
    where
      lem :  ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f ≐ id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)
      lem =
        proof≐
          ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ _ ∷ Δ) ∘ [ αJ-1 cJ' ∣ Δ ]f
        ≐⟨ ψ++ _ _ Γ (_ ∷ _ ∷ Δ) ∘ refl ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ α ⊗ id ∣ Δ ]f ∘ [ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id) ⊗ id ∣ Δ ]f ∘ [ αJ-1 cJ' ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _ ∙ (ass ∙ (refl ∘ (~ [∘∣ Δ ] _ _ ∙ [≐∣ Δ ] (~ ass)))))) ) ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ⊗ id ∘ αJ-1 cJ') ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ (~ nαJ-1 cJ')) ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ (αJ-1 cJ' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ (id ⊗ id)) ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] (~ ass ∙ (refl ∘ refl ⊗ f⊗id)) ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ α ∘ α ⊗ id ∘ αJ-1 cJ' ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ [≐∣ Δ ] ((~ αααJ-1 cJ') ∘ refl) ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ αJ-1 cJ' ∘ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ∙ ~ ass ⟩
          ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _ ⊗ _) Δ ∘ [ id ⊗ αJ-1 cJ' ∣ Δ ]f ∘ [ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ (~ nψ2 Δ (αJ-1 cJ')) ∘ refl ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∘ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f
        ≐⟨ ass ∙ (refl ∘ (refl ∘ [∘∣ Δ ] _ _ ∙ (~ ass))) ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ (ψ [ _ ∣ Δ₀ ] ([ _ ∣ Γ ] ⊗ _) Δ ∘ [ α ∣ Δ ]f ∘ [ ψ [ _ ∣ Δ₀ ] _ Γ ⊗ id ∣ Δ ]f)
        ≐⟨ refl ∘ (~ (ψ++ _ _ Γ (_ ∷ Δ))) ⟩
          id ⊗ [ αJ-1 cJ' ∣ Δ ]f ∘ ψ [ _ ∣ Δ₀ ] _ (Γ ++ _ ∷ Δ)
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
soundcmplt ρ-1 = lid

