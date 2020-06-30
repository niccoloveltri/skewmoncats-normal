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
cong-sound (Ic Γ Δ p) = cong-sound p ∘ refl
cong-sound (ufIc1 {Γ = Γ})  = refl ∘ [≐∣ Γ ] l≐ρ-1
cong-sound (IcIc {Λ = Λ}) =
  ass
  ∙ (refl
     ∘ (~ [∘∣ Λ ] _ _
       ∙ [≐∣ Λ ] nρ-1
       ∙ [∘∣ Λ ] _ _))
  ∙ ~ ass
cong-sound (⊗cIc {Λ = Λ})  =
  ass
  ∙ (refl
     ∘ (~ [∘∣ Λ ] _ _
       ∙ [≐∣ Λ ] nρ-1
       ∙ [∘∣ Λ ] _ _))
  ∙ ~ ass
cong-sound (ufIc2 {Δ = Δ}) = 
  ass
  ∙ (refl
     ∘ (~ [∘∣ Δ ] _ _
       ∙ [≐∣ Δ ] nρ-1
       ∙ [∘∣ Δ ] _ _))
  ∙ ~ ass
cong-sound IlIc = refl
cong-sound ⊗lIc = refl
cong-sound (⊗rIc1 {Γ = Γ} {Γ'} {Δ} {f = f} {g}) =
  proof≐
    (sound f ∘ [ ρ-1 ∣ Γ' ]f) ⊗ sound g ∘ φ' _ (Γ ++ I ∷ Γ') Δ
  ≐⟨ (refl ⊗ rid ∙ f⊗∘) ∘ refl ⟩ 
    sound f ⊗ sound g ∘ [ ρ-1 ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ I ∷ Γ') Δ
  ≐⟨ ass ⟩ 
    sound f ⊗ sound g ∘ ([ ρ-1 ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ I ∷ Γ') Δ)
  ≐⟨ refl ∘ nφ' Γ' Δ ρ-1 ⟩ 
    sound f ⊗ sound g ∘ (φ' _ (Γ ++ Γ') Δ ∘ [ [ ρ-1 ∣ Γ' ]f ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound f ⊗ sound g ∘ φ' _ (Γ ++ Γ') Δ ∘ [ [ ρ-1 ∣ Γ' ]f ∣ Δ ]f
  qed≐
cong-sound (⊗rIc2 {Γ = Γ} {Δ} {Δ'} {f = f} {g}) =
  proof≐
    sound f ⊗ (sound g ∘ [ ρ-1 ∣ Δ' ]f) ∘ φ' _ Γ (Δ ++ I ∷ Δ')
  ≐⟨ (rid ⊗ refl ∙ f⊗∘) ∘ refl ⟩
    sound f ⊗ sound g ∘ id ⊗ [ ρ-1 ∣ Δ' ]f ∘ φ' _ Γ (Δ ++ I ∷ Δ')
  ≐⟨ ass ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ ρ-1 ∣ Δ' ]f ∘ (ψ _ _ (Δ ++ I ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f))
  ≐⟨ refl ∘ (~ ass) ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ ρ-1 ∣ Δ' ]f ∘ ψ _ _ (Δ ++ I ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f)
  ≐⟨ refl ∘ (lem ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ (Δ ++ Δ') ∘ [ ρ-1 ∣ Δ' ]f ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f)
  ≐⟨ refl ∘ (ass ∙ (refl ∘ (~ [∘∣ Δ' ] _ _))) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ (Δ ++ Δ') ∘ [ ρ-1 ∘ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f)
  ≐⟨ refl ∘ (refl ∘ [≐∣ Δ' ] nρ-1) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ (Δ ++ Δ') ∘ [ [ ρ ∣ Δ ]f ∘ ρ-1 ∣ Δ' ]f)
  ≐⟨ refl ∘ (refl ∘ [∘∣ Δ' ] _ _  ∙ ~ ass) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ (Δ ++ Δ') ∘ [ [ ρ ∣ Δ ]f ∣ Δ' ]f ∘ [ ρ-1 ∣ Δ' ]f) 
  ≐⟨ ~ ass ⟩
    sound f ⊗ sound g ∘ φ' _ Γ (Δ ++ Δ') ∘ [ ρ-1 ∣ Δ' ]f
  qed≐
  where
    lem : ∀ {A} →
      id ⊗ [ ρ-1 ∣ Δ' ]f ∘ ψ A I (Δ ++ I ∷ Δ')
      ≐ ψ A I (Δ ++ Δ') ∘ [ ρ-1 ∣ Δ' ]f
    lem {A} =
      proof≐
        id ⊗ [ ρ-1 ∣ Δ' ]f ∘ ψ A I (Δ ++ I ∷ Δ')
      ≐⟨ refl ∘ ψ++ A I (Δ ++ I ∷ []) Δ' ⟩
        id ⊗ [ ρ-1 ∣ Δ' ]f ∘ (ψ A ([ I ∣ Δ ] ⊗ I) Δ' ∘ [ ψ A I (Δ ++ I ∷ []) ∣ Δ' ]f)
      ≐⟨ ~ ass ⟩
        id ⊗ [ ρ-1 ∣ Δ' ]f ∘ ψ A ([ I ∣ Δ ] ⊗ I) Δ' ∘ [ ψ A I (Δ ++ I ∷ []) ∣ Δ' ]f
      ≐⟨ nψ2 Δ' ρ-1 ∘ refl ⟩
        ψ A [ I ∣ Δ ] Δ' ∘ [ id ⊗ ρ-1 ∣ Δ' ]f ∘ [ ψ A I (Δ ++ I ∷ []) ∣ Δ' ]f
      ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Δ' ] _ _)) ⟩
        ψ A [ I ∣ Δ ] Δ' ∘ [ id ⊗ ρ-1 ∘ ψ A I (Δ ++ I ∷ []) ∣ Δ' ]f
      ≐⟨ refl ∘ [≐∣ Δ' ] (refl ∘ ψ++ A I Δ (I ∷ [])) ⟩
        ψ A [ I ∣ Δ ] Δ' ∘ [ id ⊗ ρ-1 ∘ (id ∘ α ∘ ψ A I Δ ⊗ id) ∣ Δ' ]f
      ≐⟨ refl ∘ [≐∣ Δ' ] (~ ass ∙ (refl ∘ lid ∘ refl)) ⟩
        ψ A [ I ∣ Δ ] Δ' ∘ [ id ⊗ ρ-1 ∘ α ∘ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ refl ∘ [≐∣ Δ' ] (ρα-1 ∘ refl) ⟩
        ψ A [ I ∣ Δ ] Δ' ∘ [ ρ-1 ∘ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ refl ∘ [≐∣ Δ' ] nρ-1 ⟩
        ψ A [ I ∣ Δ ] Δ' ∘ [ ψ A I Δ ∘ ρ-1 ∣ Δ' ]f
      ≐⟨ refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass ⟩
        ψ A [ I ∣ Δ ] Δ' ∘ [ ψ A I Δ ∣ Δ' ]f ∘ [ ρ-1 ∣ Δ' ]f
      ≐⟨ (~ ψ++ A I Δ Δ') ∘ refl ⟩
        ψ A I (Δ ++ Δ') ∘ [ ρ-1 ∣ Δ' ]f
      qed≐
cong-sound (⊗c Γ Δ cJ cJ' p) = cong-sound p ∘ refl 
cong-sound (uf⊗c1 {Γ = Γ}{cJ' = cJ'}) =
  refl ∘ ([≐∣ Γ ] lem ∙ [∘∣ Γ ] _ _)
  ∙ ~ ass
  where
    lem : l ≐ l ⊗ id ∘ αJ-1 cJ'
    lem =
      rid
      ∙ (refl ∘ ~ ααJ-1 cJ')
      ∙ ~ ass
      ∙ (lα ∘ refl)
cong-sound (⊗c⊗c {Λ = Λ}{cK' = cK'}) =
  ass
  ∙ (refl
     ∘ (~ [∘∣ Λ ] _ _
       ∙ [≐∣ Λ ] (refl ∘ refl ⊗ (~ f⊗id) ∙ nαJ-1 cK')
       ∙ [∘∣ Λ ] _ _))
  ∙ ~ ass
cong-sound (Ic⊗c {Λ = Λ}{cJ' = cJ'}) =
  ass
  ∙ (refl
     ∘ (~ [∘∣ Λ ] _ _
       ∙ [≐∣ Λ ] (refl ∘ refl ⊗ (~ f⊗id) ∙ nαJ-1 cJ')
       ∙ [∘∣ Λ ] _ _))
  ∙ ~ ass
cong-sound (uf⊗c2 {Δ = Δ}{cJ' = cJ'}) =
  ass
  ∙ (refl
     ∘ (~ [∘∣ Δ ] _ _
       ∙ [≐∣ Δ ] (refl ∘ refl ⊗ (~ f⊗id) ∙ nαJ-1 cJ')
       ∙ [∘∣ Δ ] _ _))
  ∙ ~ ass
cong-sound Il⊗c = refl
cong-sound ⊗l⊗c = refl
cong-sound (⊗r⊗c1 {Γ = Γ} {Γ'} {Δ} {J = J}{J'}{cJ} {cJ'} {f} {g}) =
  proof≐
    (sound f ∘ [ αJ-1 cJ' ∣ Γ' ]f) ⊗ sound g ∘ φ' _ (Γ ++ J ⊗ J' ∷ Γ') Δ
  ≐⟨ (refl ⊗ rid ∙ f⊗∘) ∘ refl ⟩ 
    sound f ⊗ sound g ∘ [ αJ-1 cJ' ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ J ⊗ J' ∷ Γ') Δ
  ≐⟨ ass ⟩ 
    sound f ⊗ sound g ∘ ([  αJ-1 cJ' ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ J ⊗ J' ∷ Γ') Δ)
  ≐⟨ refl ∘ nφ' Γ' Δ  (αJ-1 cJ') ⟩ 
    sound f ⊗ sound g ∘ (φ' _ (Γ ++ J ∷ J' ∷ Γ') Δ ∘ [ [  αJ-1 cJ' ∣ Γ' ]f ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound f ⊗ sound g ∘ φ' _ (Γ ++ J ∷ J' ∷ Γ') Δ ∘ [ [ αJ-1 cJ' ∣ Γ' ]f ∣ Δ ]f
  qed≐
cong-sound (⊗r⊗c2 {S}{Γ = Γ} {Δ} {Δ'} {J = J} {J'} {cJ} {cJ'} {f} {g}) = 
  proof≐
    sound f ⊗ (sound g ∘ [ αJ-1 cJ' ∣ Δ' ]f) ∘ φ' _ Γ (Δ ++ J ⊗ J' ∷ Δ')
  ≐⟨ (rid ⊗ refl ∙ f⊗∘) ∘ refl ⟩
    sound f ⊗ sound g ∘ id ⊗ [ αJ-1 cJ' ∣ Δ' ]f ∘ φ' _ Γ (Δ ++ J ⊗ J' ∷ Δ')
  ≐⟨ ass ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ αJ-1 cJ' ∣ Δ' ]f ∘ (ψ _ I (Δ ++ J ⊗ J' ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f))
  ≐⟨ refl ∘ (~ ass) ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ αJ-1 cJ' ∣ Δ' ]f ∘ ψ _ I (Δ ++ J ⊗ J' ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f)
  ≐⟨ refl ∘ (lem ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ I (Δ ++ J ∷ J' ∷ Δ') ∘ [ αJ-1 cJ' ∣ Δ' ]f ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f)
  ≐⟨ refl ∘ (ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)) ⟩
    sound f ⊗ sound g ∘ (ψ _ I (Δ ++ J ∷ J' ∷ Δ') ∘ [ αJ-1 cJ' ∘ [ ρ ∣ Δ ]f ⊗ id ∣ Δ' ]f)
  ≐⟨ refl ∘ (refl ∘ [≐∣ Δ' ] (refl ∘ refl ⊗ (~ f⊗id) ∙ nαJ-1 cJ')) ⟩
    sound f ⊗ sound g ∘ (ψ _ I (Δ ++ J ∷ J' ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ⊗ id ∘ αJ-1 cJ' ∣ Δ' ]f)
  ≐⟨ refl ∘ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass) ⟩
    sound f ⊗ sound g ∘ (ψ _ I (Δ ++ J ∷ J' ∷ Δ') ∘ [ [ ρ ∣ Δ ]f ⊗ id ⊗ id ∣ Δ' ]f ∘ [ αJ-1 cJ' ∣ Δ' ]f) 
  ≐⟨ ~ ass ⟩
    sound f ⊗ sound g ∘ φ' _ Γ (Δ ++ J ∷ J' ∷ Δ') ∘ [ αJ-1 cJ' ∣ Δ' ]f
  qed≐
  where
    lem : ∀ {A} →
      id ⊗ [ αJ-1 cJ' ∣ Δ' ]f ∘ ψ A I (Δ ++ J ⊗ J' ∷ Δ')
      ≐ ψ A I (Δ ++ J ∷ J' ∷ Δ') ∘ [ αJ-1 cJ' ∣ Δ' ]f
    lem {A} =
      proof≐
        id ⊗ [ αJ-1 cJ' ∣ Δ' ]f ∘ ψ A I (Δ ++ J ⊗ J' ∷ Δ')
      ≐⟨ refl ∘ ψ++ A I Δ (J ⊗ J' ∷ Δ') ⟩
        id ⊗ [ αJ-1 cJ' ∣ Δ' ]f ∘ (ψ A ([ I ∣ Δ ] ⊗ (J ⊗ J')) Δ' ∘ [ α ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f)
      ≐⟨ ~ ass ∙ ((~ ass) ∘ refl) ⟩
        id ⊗ [ αJ-1 cJ' ∣ Δ' ]f ∘ ψ A ([ I ∣ Δ ] ⊗ (J ⊗ J')) Δ' ∘ [ α ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ nψ2 Δ' (αJ-1 cJ') ∘ refl ∘ refl ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ id ⊗ αJ-1 cJ' ∣ Δ' ]f ∘ [ α ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ (ass ∙ (refl ∘ (~ [∘∣ Δ' ] _ _))) ∘ refl ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ id ⊗ αJ-1 cJ' ∘ α ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ refl ∘ [≐∣ Δ' ] (αααJ-1 cJ') ∘ refl ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∘ α ⊗ id ∘ αJ-1 cJ' ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ ((refl ∘ [≐∣ Δ' ] ass ∙ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass)) ∙ (refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass)) ∘ refl ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∣ Δ' ]f ∘ [ α ⊗ id  ∣ Δ' ]f ∘ [ αJ-1 cJ' ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ∣ Δ' ]f
      ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Δ' ] _ _ ∙ [≐∣ Δ' ] (refl ∘ refl ⊗ (~ f⊗id)))) ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∣ Δ' ]f ∘ [ α ⊗ id  ∣ Δ' ]f ∘ [ αJ-1 cJ' ∘  ψ A I Δ ⊗ (id ⊗ id) ∣ Δ' ]f
      ≐⟨ refl ∘ [≐∣ Δ' ] (nαJ-1 cJ') ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∣ Δ' ]f ∘ [ α ⊗ id  ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ⊗ id ∘ αJ-1 cJ' ∣ Δ' ]f
      ≐⟨ refl ∘ [∘∣ Δ' ] _ _ ∙ ~ ass ⟩
        ψ A ([ I ∣ Δ ] ⊗ J ⊗ J') Δ' ∘ [ α ∣ Δ' ]f ∘ [ α ⊗ id  ∣ Δ' ]f ∘ [ ψ A I Δ ⊗ id ⊗ id ∣ Δ' ]f ∘ [ αJ-1 cJ' ∣ Δ' ]f
      ≐⟨ (~ ψ++ A I Δ (J ∷ J' ∷ Δ')) ∘ refl ⟩
        ψ A I (Δ ++ J ∷ J' ∷ Δ') ∘ [ αJ-1 cJ' ∣ Δ' ]f
      qed≐

