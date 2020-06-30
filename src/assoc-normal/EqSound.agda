{-# OPTIONS --rewriting #-}

module EqSound where

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
open import Sound

-- ====================================================================

-- The soundness map sends ≗-related derivations to ≐-related
-- derivations.

cong-sound : ∀{S Γ C} {f g : S ∣ Γ ⊢ C} → f ≗ g → sound f ≐ sound g
cong-sound refl = refl
cong-sound (~ p) = ~ cong-sound p
cong-sound (p ∙ p₁) = cong-sound p ∙ cong-sound p₁
cong-sound (uf p) = cong-sound p ∘ refl
cong-sound (⊗l p) = cong-sound p
cong-sound (Il p) = cong-sound p
cong-sound (⊗r p p₁) = cong-sound p ⊗ cong-sound p₁ ∘ refl
cong-sound axI = refl
cong-sound ax⊗ = lαρ ∙ ~ (refl ⊗ lid ∘ lid ∘ refl) ∙ ass
cong-sound (⊗ruf {Γ}{Δ}{A}{A'}{B}{f}{g}) =
  proof≐
    ((sound f ∘ [ l ∣ Γ ]f) ⊗ sound g) ∘ φ' (I ⊗ A') Γ Δ
  ≐⟨ refl ⊗ rid ∘ refl ⟩
    ((sound f ∘ [ l ∣ Γ ]f) ⊗ (sound g ∘ id)) ∘ φ' (I ⊗ A') Γ Δ
  ≐⟨ f⊗∘ ∘ refl ⟩
    (sound f ⊗ sound g) ∘ ([ l ∣ Γ ]f ⊗ id) ∘ φ' (I ⊗ A') Γ Δ
  ≐⟨ ass ⟩
    (sound f ⊗ sound g) ∘ (([ l ∣ Γ ]f ⊗ id) ∘ φ' (I ⊗ A') Γ Δ)
  ≐⟨ refl ∘ nφ' Γ Δ l ⟩ 
    (sound f ⊗ sound g) ∘ (φ' A' Γ Δ ∘ [ l ∣ Γ ++ Δ ]f)
  ≐⟨ ~ ass ⟩
    (sound f ⊗ sound g) ∘ φ' A' Γ Δ ∘ [ l ∣ Γ ++ Δ ]f
  qed≐
cong-sound ⊗rIl = refl
cong-sound ⊗r⊗l = refl
cong-sound (⊗c Γ Δ p) = cong-sound p ∘ refl 
cong-sound (uf⊗c1 {Γ = Γ}) =
  refl ∘ ([≐∣ Γ ] lem ∙ [∘∣ Γ ] _ _)
  ∙ ~ ass
  where
    lem : l ≐ l ⊗ id ∘ α-1
    lem =
      rid
      ∙ (refl ∘ ~ αα-1)
      ∙ ~ ass
      ∙ (lα ∘ refl)
cong-sound (⊗c⊗c {Λ = Λ}) =
  ass
  ∙ (refl
     ∘ (~ [∘∣ Λ ] _ _
       ∙ [≐∣ Λ ] (refl ∘ refl ⊗ (~ f⊗id) ∙ nα-1)
       ∙ [∘∣ Λ ] _ _))
  ∙ ~ ass
cong-sound (uf⊗c2 {Δ = Δ}) =
  ass
  ∙ (refl
     ∘ (~ [∘∣ Δ ] _ _
       ∙ [≐∣ Δ ] (refl ∘ refl ⊗ (~ f⊗id) ∙ nα-1)
       ∙ [∘∣ Δ ] _ _))
  ∙ ~ ass
cong-sound Il⊗c = refl
cong-sound ⊗l⊗c = refl
cong-sound (⊗r⊗c1 {Γ = Γ} {Γ'} {Δ} {J = J}{J'} {f} {g}) =
  proof≐
    (sound f ∘ [ α-1 ∣ Γ' ]f) ⊗ sound g ∘ φ' _ (Γ ++ J ⊗ J' ∷ Γ') Δ
  ≐⟨ (refl ⊗ rid ∙ f⊗∘) ∘ refl ⟩ 
    sound f ⊗ sound g ∘ [ α-1 ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ J ⊗ J' ∷ Γ') Δ
  ≐⟨ ass ⟩ 
    sound f ⊗ sound g ∘ ([  α-1 ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ J ⊗ J' ∷ Γ') Δ)
  ≐⟨ refl ∘ nφ' Γ' Δ  α-1 ⟩ 
    sound f ⊗ sound g ∘ (φ' _ (Γ ++ J ∷ J' ∷ Γ') Δ ∘ [ [  α-1 ∣ Γ' ]f ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound f ⊗ sound g ∘ φ' _ (Γ ++ J ∷ J' ∷ Γ') Δ ∘ [ [ α-1 ∣ Γ' ]f ∣ Δ ]f
  qed≐
cong-sound (⊗r⊗c2 {S}{Γ = Γ} {Δ} {Δ'} {J = J} {J'} {f} {g}) = 
  proof≐
    sound f ⊗ (sound g ∘ [ α-1 ∣ Δ' ]f) ∘ φ' _ Γ (Δ ++ J ⊗ J' ∷ Δ')
  ≐⟨ (rid ⊗ refl ∙ f⊗∘) ∘ refl ⟩
    sound f ⊗ sound g ∘ id ⊗ [ α-1 ∣ Δ' ]f ∘ φ' _ Γ (Δ ++ J ⊗ J' ∷ Δ')
  ≐⟨ ass ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ α-1 ∣ Δ' ]f ∘ (ψ _ I (Δ ++ J ⊗ J' ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f))
  ≐⟨ refl ∘ (~ ass) ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ α-1 ∣ Δ' ]f ∘ ψ _ I (Δ ++ J ⊗ J' ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f)
  ≐⟨ refl ∘ (lem ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ I (Δ ++ J ∷ J' ∷ Δ') ∘ [ α-1 ∣ Δ' ]f ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f)
  ≐⟨ refl ∘ (ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)) ⟩
    sound f ⊗ sound g ∘ (ψ _ I (Δ ++ J ∷ J' ∷ Δ') ∘ [ α-1 ∘ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f)
  ≐⟨ refl ∘ (refl ∘ [≐∣ Δ' ] (refl ∘ refl ⊗ (~ f⊗id) ∙ nα-1)) ⟩
    sound f ⊗ sound g ∘ (ψ _ I (Δ ++ J ∷ J' ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ⊗ id ∘ α-1 ∣ Δ' ]f)
  ≐⟨ refl ∘ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass) ⟩
    sound f ⊗ sound g ∘ (ψ _ I (Δ ++ J ∷ J' ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ⊗ id ∣ Δ' ]f ∘ [ α-1 ∣ Δ' ]f) 
  ≐⟨ ~ ass ⟩
    sound f ⊗ sound g ∘ φ' _ Γ (Δ ++ J ∷ J' ∷ Δ') ∘ [ α-1 ∣ Δ' ]f
  qed≐
  where
    lem : ∀ {A} →
      id ⊗ [ α-1 ∣ Δ' ]f ∘ ψ A I (Δ ++ J ⊗ J' ∷ Δ')
      ≐ ψ A I (Δ ++ J ∷ J' ∷ Δ') ∘ [ α-1 ∣ Δ' ]f
    lem {A} =
      proof≐
        id ⊗ [ α-1 ∣ Δ' ]f ∘ ψ A I (Δ ++ J ⊗ J' ∷ Δ')
      ≐⟨ refl ∘ ψ++ A I Δ (J ⊗ J' ∷ Δ') ⟩
        id ⊗ [ α-1 ∣ Δ' ]f ∘ (ψ A ([ I ∣ Δ ] ⊗ (J ⊗ J')) Δ' ∘ [ α ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f)
      ≐⟨ ~ ass ∙ ((~ ass) ∘ refl) ⟩
        id ⊗ [ α-1 ∣ Δ' ]f ∘ ψ A ([ I ∣ Δ ] ⊗ (J ⊗ J')) Δ' ∘ [ α ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ nψ2 Δ' (α-1) ∘ refl ∘ refl ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ id ⊗ α-1 ∣ Δ' ]f ∘ [ α ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ (ass ∙ (refl ∘ (~ [∘∣ Δ' ] _ _))) ∘ refl ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ id ⊗ α-1 ∘ α ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ refl ∘ [≐∣ Δ' ] ααα-1 ∘ refl ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∘ α ⊗ id ∘ α-1 ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ ((refl ∘ [≐∣ Δ' ] ass ∙ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass)) ∙ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass)) ∘ refl ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∣ Δ' ]f ∘ [ α ⊗ id  ∣ Δ' ]f ∘ [ α-1 ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Δ' ] _ _ ∙ [≐∣ Δ' ] (refl ∘ refl ⊗ (~ f⊗id)))) ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∣ Δ' ]f ∘ [ α ⊗ id  ∣ Δ' ]f ∘ [ α-1 ∘  ψ A I Δ ⊗ (id ⊗ id) ∣ Δ' ]f
      ≐⟨ refl ∘ [≐∣ Δ' ] (nα-1) ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∣ Δ' ]f ∘ [ α ⊗ id  ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ⊗ id ∘ α-1 ∣ Δ' ]f
      ≐⟨ refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∣ Δ' ]f ∘ [ α ⊗ id  ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ⊗ id ∣ Δ' ]f ∘ [ α-1 ∣ Δ' ]f
      ≐⟨ (~ ψ++ A I Δ (J ∷ J' ∷ Δ')) ∘ refl ⟩
        ψ A I (Δ ++ J ∷ J' ∷ Δ') ∘ [ α-1 ∣ Δ' ]f
      qed≐

