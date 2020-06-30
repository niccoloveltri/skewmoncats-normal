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
open import Sound
open import Complete
open import StrongComplete

-- Interaction of the soundness map with admissible rules, such as the
-- cut rules, uf-1, ⊗rL, etc.

[scut] : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
           [ A ∣ Δ ] ⇒ C → 〈 S ∣ Γ 〉 ⇒ A  → 〈 S ∣ Γ ++ Δ 〉 ⇒ C
[scut] {Δ = Δ} g f = g ∘ [ f ∣ Δ ]f 

[ccut] : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
         〈  T ∣ Δ 〉  ⇒ C  → [ I ∣ Γ ] ⇒ A →  Δ ≡ Δ₀ ++ A ∷ Δ' →
                                         〈 T ∣ Δ₀ ++ Γ ++ Δ' 〉 ⇒ C
[ccut] {T} {Γ} Δ₀ {Δ'} g f refl = g ∘ [ id ⊗ f ∘ φ T Δ₀ Γ ∣ Δ' ]f 


sound-uf-1' : {Γ Γ' : Cxt} {A C : Fma}
  → (f : nothing ∣ Γ' ⊢L C) (r : Γ' ≡ A ∷ Γ)
  → sound (uf-1' f r) ≐ sound (subst-cxt r f) ∘ [ l-1 ∣ Γ ]f
sound-uf-1' {Γ} (uf f) refl =
  rid
  ∙ (refl ∘ (~ [id∣ Γ ] ∙ ([≐∣ Γ ] (~ ll-1) ∙ [∘∣ Γ ] _ _)))
  ∙ ~ ass


mutual
  soundscut : {S : Stp} → {Γ : Cxt} → (Δ' : Cxt) {A C : Fma} → 
       (f : S ∣ Γ ⊢L A) → (g : just A ∣ Δ' ⊢L C) → 
                 sound (scut f g) ≐ [scut] {S} {Γ} {Δ'} (sound g) (sound f)                 
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
  soundscut Δ (Il f) g = soundscut Δ f g
  soundscut Δ (⊗l f) g = soundscut Δ f g
  soundscut Δ (switch-at f) g = soundscutR Δ f g
  soundscut Δ (switch-not f) g = soundscutR Δ f g

  soundscutR : {S : StpR} → {Γ : Cxt} → (Δ' : Cxt) {A C : Fma} → 
       (f : S ∣ Γ ⊢R A) → (g : just A ∣ Δ' ⊢L C) → 
                 sound (scutR f g) ≐ [scut] {mmap ` S} {Γ} {Δ'} (sound g) (soundR f)                 
  soundscutR Δ ax g = rid ∙ (refl ∘ ~ [id∣ Δ ])
  soundscutR Δ Ir (Il g) = rid ∙ (refl ∘ ~ [id∣ Δ ])
  soundscutR Δ (⊗r {Γ = Γ'}{Δ'} f f') (⊗l g) =
    proof≐
      sound (scutR f (ccut [] f' g refl))
    ≐⟨ soundscutR (Δ' ++ Δ) f (ccut [] f' g refl) ⟩
      sound (ccut [] f' g refl) ∘ [ soundR f ∣ Δ' ++ Δ ]f
    ≐⟨ soundccut [] f' g refl ∘ refl ⟩
      sound g ∘ [ id ⊗ sound f' ∘ φ' _ [] Δ' ∣ Δ ]f ∘ [ [ soundR f ∣ Δ' ]f ∣ Δ ]f
    ≐⟨ ass ⟩
      sound g ∘ ([ id ⊗ sound f' ∘ φ' _ [] Δ' ∣ Δ ]f ∘ [ [ soundR f ∣ Δ' ]f ∣ Δ ]f)
    ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩
      sound g ∘ [ id ⊗ sound f' ∘ φ' _ [] Δ' ∘ [ soundR f ∣ Δ' ]f ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] ass ⟩
      sound g ∘ [ id ⊗ sound f' ∘ (φ' _ [] Δ' ∘ [ soundR f ∣ Δ' ]f) ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ ~ (nφ' [] Δ' (soundR f))) ⟩
      sound g ∘ [ id ⊗ sound f' ∘ (soundR f ⊗ id ∘ φ' _ [] Δ') ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (~ ass) ⟩
      sound g ∘ [ id ⊗ sound f' ∘ soundR f ⊗ id ∘ φ' _ [] Δ' ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (~ f⊗∘ ∘ refl) ⟩
      sound g ∘ [ (id ∘ soundR f) ⊗ (sound f' ∘ id) ∘ φ' _ [] Δ' ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (lid ⊗ (~ rid) ∘ refl) ⟩
      sound g ∘ [ soundR f ⊗ sound f' ∘ φ' _ Γ' Δ' ∣ Δ ]f
    qed≐  
  soundscutR Δ (⊗r[] f f') (⊗l g) =
    proof≐
      sound (scutR f' (uf-1 (scutR f g)))
    ≐⟨ soundscutR Δ f' (uf-1 (scutR f g)) ⟩
      sound (uf-1' (scutR f g) refl) ∘ [ soundR f' ∣ Δ ]f
    ≐⟨ sound-uf-1' (scutR f g) refl ∘ refl ⟩
      sound (scutR f g) ∘ [ l-1 ∣ Δ ]f  ∘ [ soundR f' ∣ Δ ]f
    ≐⟨ soundscutR (_ ∷ Δ) f g ∘ refl ∘ refl ⟩
      sound g  ∘ [ soundR f ⊗ id ∣ Δ ]f ∘ [ l-1 ∣ Δ ]f  ∘ [ soundR f' ∣ Δ ]f
    ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _) ∘ refl ⟩
      sound g ∘ [ soundR f ⊗ id ∘ l-1 ∣ Δ ]f ∘ [ soundR f' ∣ Δ ]f
    ≐⟨ ass ⟩
      sound g ∘ ([ soundR f ⊗ id ∘ l-1 ∣ Δ ]f ∘ [ soundR f' ∣ Δ ]f)
    ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩
      sound g ∘ [ soundR f ⊗ id ∘ l-1 ∘ soundR f' ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (ass ∙ (refl ∘ nl-1) ∙ ~ ass) ⟩
      sound g ∘ [ soundR f ⊗ id ∘ id ⊗ soundR f' ∘ l-1 ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (~ f⊗∘ ∙ ~ rid ⊗ (~ lid) ∘ refl) ⟩
      sound g ∘ [ soundR f ⊗ soundR f' ∘ l-1 ∣ Δ ]f
    qed≐

  soundccut : {T : Stp} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma}  → 
       (f : nothing ∣ Γ ⊢L A) → (g : T ∣ Δ ⊢L C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
              sound (ccut Δ₀ f g p) ≐ sound (subst-cxt p g) ∘ [ id ⊗ sound f ∘ φ T Δ₀ Γ ∣ Δ' ]f
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
  soundccut Δ₀ f (Il g) refl = soundccut Δ₀ f g refl
  soundccut Δ₀ f (⊗l g) refl = soundccut (_ ∷ Δ₀) f g refl
  soundccut Δ₀ f (switch-at g) refl = soundccutR Δ₀ f g refl
  soundccut Δ₀ f (switch-not g) p = ⊥-elim ([]disj∷ Δ₀ p)

  soundccutR : {T : StpR} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma}  → 
       (f : nothing ∣ Γ ⊢L A) → (g : T ∣ Δ ⊢R C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
              soundR (ccutR Δ₀ f g p)
              ≐
              soundR (subst-cxtR p g) ∘ [ id ⊗ sound f ∘ φ (mmap ` T) Δ₀ Γ ∣ Δ' ]f
  soundccutR Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
  soundccutR Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
  soundccutR Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
  soundccutR {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
    proof≐
      soundR (ccutR Δ₀ f g refl) ⊗ sound g' ∘ φ' _ Γ₀ Δ
    ≐⟨ soundccutR Δ₀ f g refl ⊗ refl ∘ refl ⟩ 
      (soundR g ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f) ⊗ sound g' ∘ φ' _ Γ₀ Δ
    ≐⟨ refl ⊗ rid ∙ f⊗∘ ∘ refl ⟩ 
      soundR g ⊗ sound g' ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ
    ≐⟨ refl ∘ refl ∙ ass ⟩ 
      soundR g ⊗ sound g' ∘ ([ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ)
    ≐⟨ refl ∘ nφ' Γ₀ Δ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⟩ 
      soundR g ⊗ sound g' ∘ (φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ∣ Δ ]f)
    ≐⟨ ~ ass ⟩ 
      soundR g ⊗ sound g' ∘ φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ∣ Δ ]f
    qed≐
  soundccutR {Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
    proof≐
      soundR g ⊗ sound (ccut Γ₀ f g' refl) ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
    ≐⟨ refl ⊗ soundccut Γ₀ f g' refl ∘ refl ⟩ 
      soundR g ⊗ (sound g' ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f) ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
    ≐⟨ rid ⊗ refl ∙ f⊗∘ ∘ refl ⟩ 
      soundR g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
    ≐⟨ refl ∘ (refl ⊗ [∘∣ Δ' ] _ _ ∙ (rid ⊗ refl ∙ f⊗∘)) ∙ ~ ass ∘ refl ∙ ass ⟩ 
      soundR g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (id ⊗ [ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ'))
    ≐⟨ refl ∘ assφ' Γ Γ₀ Γ₁ Δ' ⟩ 
      soundR g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f)
    ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩ 
      soundR g ⊗ sound g' ∘ (id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ')) ∘ [ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f
    ≐⟨ refl ∘ nφ'2 Γ Γ₀ Δ' (sound f) ∘ refl ⟩ 
      soundR g ⊗ sound g' ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∣ Δ' ]f) ∘ [ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f
    ≐⟨ ~ ass ∘ refl ∙ ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)  ⟩ 
      soundR g ⊗ sound g' ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∘ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f
    qed≐
  soundccutR {Γ = Γ} Δ₀ {Δ'} f (⊗r[] g g') refl =
    proof≐
      soundR g ⊗ soundR (ccutR Δ₀ f g' refl) ∘ l-1
    ≐⟨ rid ⊗ (~ lid) ∙ f⊗∘ ∘ refl ⟩
      soundR g ⊗ id ∘ id ⊗ soundR (ccutR Δ₀ f g' refl) ∘ l-1
    ≐⟨ refl ∘ refl ⊗ soundccutR Δ₀ f g' refl ∘ refl ⟩
      soundR g ⊗ id ∘ id ⊗ (soundR g' ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Δ' ]f) ∘ l-1
    ≐⟨ refl ∘ rid ⊗ refl ∙ (refl ∘ f⊗∘ ∙ ~ ass) ∘ refl ⟩
      soundR g ⊗ id ∘ id ⊗ soundR g' ∘ id ⊗ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Δ' ]f ∘ l-1
    ≐⟨ ~ f⊗∘ ∙ (~ rid) ⊗ lid ∘ refl ∘ refl ⟩
      soundR g ⊗ soundR g' ∘ id ⊗ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Δ' ]f ∘ l-1
    ≐⟨ ass ∙ (refl ∘ ~ nl-1) ∙ ~ ass ⟩
      soundR g ⊗ soundR g' ∘ l-1 ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Δ' ]f
    qed≐

mutual
  sound-⊗rL : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ⊢L A) (g : nothing ∣ Δ ⊢L B)
    → sound (⊗rL f g) ≐ sound f ⊗ sound g ∘ φ S Γ Δ
  sound-⊗rL {Δ = Δ} (uf {Γ} f) g =
    proof≐
      sound (⊗rL f g) ∘ [ [ l ∣ Γ ]f ∣ Δ ]f
    ≐⟨ sound-⊗rL f g ∘ refl ⟩
      sound f ⊗ sound g ∘ φ' _ Γ Δ ∘ [ [ l ∣ Γ ]f ∣ Δ ]f
    ≐⟨ ass ⟩
      sound f ⊗ sound g ∘ (φ' _ Γ Δ ∘ [ [ l ∣ Γ ]f ∣ Δ ]f)
    ≐⟨ refl ∘ ~ (nφ' Γ Δ l) ⟩
      sound f ⊗ sound g ∘ ([ l ∣ Γ ]f ⊗ id ∘ φ' _ Γ Δ)
    ≐⟨ ~ ass ⟩
      sound f ⊗ sound g ∘ [ l ∣ Γ ]f ⊗ id ∘ φ nothing (_ ∷ Γ) Δ
    ≐⟨ ~ f⊗∘ ∙ refl ⊗ (~ rid) ∘ refl ⟩
    (sound f ∘ [ l ∣ Γ ]f) ⊗ sound g ∘ φ nothing (_ ∷ Γ) Δ
    qed≐
  sound-⊗rL (Il f) g = sound-⊗rL f g
  sound-⊗rL (⊗l f) g = sound-⊗rL f g
  sound-⊗rL (switch-at f) g = refl
  sound-⊗rL (switch-not f) (uf {Γ} g) =
    proof≐
      sound (⊗r[]L (switch-not f) g) ∘ [ l ∣ Γ ]f
    ≐⟨ sound-⊗r[]L (switch-not f) g ∘ refl ⟩ 
      soundR f ⊗ sound g ∘ l-1 ∘ [ l ∣ Γ ]f
    ≐⟨ ass ⟩ 
      soundR f ⊗ sound g ∘ (l-1 ∘ [ l ∣ Γ ]f)
    ≐⟨ refl ∘ nl-1 ⟩ 
      soundR f ⊗ sound g ∘ (id ⊗ [ l ∣ Γ ]f ∘ l-1 )
    ≐⟨ refl ∘ (refl ∘ (rid ∙ (refl ∘ ~ lφ' (_ ∷ Γ) ∙ (~ ass ∙ (l-1l ∘ refl ∙ lid))))) ⟩ 
      soundR f ⊗ sound g ∘ (id ⊗ [ l ∣ Γ ]f ∘ φ' _ [] (_ ∷ Γ))
    ≐⟨ ~ ass ∙ (~ f⊗∘ ∘ refl) ∙ ((~ rid) ⊗ refl ∘ refl) ⟩ 
      soundR f ⊗ (sound g ∘ [ l ∣ Γ ]f) ∘ φ' _ [] (_ ∷ Γ)
    qed≐
  sound-⊗rL (switch-not f) (switch-not f₁) = refl

  sound-⊗r[]L : {Δ : Cxt} {A' A B : Fma}
    → (f : nothing ∣ [] ⊢L A) (g : just A' ∣ Δ ⊢L B)
    → sound (⊗r[]L f g) ≐ sound f ⊗ sound g ∘ l-1
  sound-⊗r[]L {Δ} f (Il g) = sound-⊗rL f g ∙ (refl ∘ (~ lid ∙ (~ l-1l ∘ refl ∙ (ass ∙ (refl ∘ lφ' Δ ∙ ~ rid)))))
  sound-⊗r[]L f (⊗l g) = sound-⊗r[]L f g
  sound-⊗r[]L (switch-not f) (switch-at g) = refl

sound-axL : {A : Fma} → sound axL ≐ id {A}
sound-axL {` X} = refl
sound-axL {I} = refl
sound-axL {A ⊗ B} =
  sound-⊗rL axL _
  ∙ (sound-axL ⊗ (sound-axL ∘ refl ∙  lid) ∘ (ass ∙ lid))
  ∙ ~ (lαρ ∙ ass)


soundcmplt : {A B : Fma} (f : A ⇒ B)
  → sound (cmplt f) ≐ f
soundcmplt id = sound-axL
soundcmplt (f ∘ g) =
  soundscut [] (cmplt g) (cmplt f)
  ∙ (soundcmplt f ∘ soundcmplt g)
soundcmplt (f ⊗ g) =
  sound-⊗rL (cmplt f) (uf (cmplt g))
  ∙ (soundcmplt f ⊗ (soundcmplt g ∘ refl) ∘ refl)
  ∙ (rid ⊗ refl ∙ f⊗∘ ∘ refl)
  ∙ ass
  ∙ (refl ∘ (refl ∘ (lid ∘ refl) ∙ (~ ass ∙ ~ lαρ)))
  ∙ ~ rid
soundcmplt l = sound-axL ∘ refl ∙ lid
soundcmplt ρ = 
  sound-⊗rL axL (switch-not Ir)
  ∙ (sound-axL ⊗ refl
  ∙ f⊗id ∘ refl ∙ (lid ∙ lid))
soundcmplt α =
  proof≐
    sound (⊗rL axL (uf (⊗rL axL (uf axL))))
  ≐⟨ sound-⊗rL axL _ ⟩
    sound axL ⊗ (sound (⊗rL axL (uf axL)) ∘ l ⊗ id) ∘ (id ∘ α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
  ≐⟨ sound-axL ⊗ (sound-⊗rL axL _ ∘ refl) ∘ refl ⟩
    id ⊗ (sound axL ⊗ (sound axL ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id) ∘ l ⊗ id) ∘ (id ∘ α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
  ≐⟨ refl ⊗ (sound-axL ⊗ (sound-axL ∘ refl) ∘ refl ∘ refl) ∘ refl ⟩
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
soundcmplt l-1 =
  sound-⊗r[]L (switch-not Ir) axL
  ∙ (refl ⊗ sound-axL ∙ f⊗id ∘ refl)
  ∙ lid

-- ====================================================================

-- sound ∘ ⊗l-1⋆ is equal to sound


soundIl-1 : {Γ : Cxt}{C : Fma}{f : just I ∣ Γ ⊢L C}
  → sound (Il-1 f) ≐ sound f
soundIl-1 {f = Il f} = refl

sound⊗l-1 : {Γ : Cxt}{A B C : Fma}{f : just (A ⊗ B) ∣ Γ ⊢L C}
  → sound (⊗l-1 f) ≐ sound f
sound⊗l-1 {f = ⊗l f} = refl

sound⊗l-1⋆ : {S : Stp}{Γ : Cxt}{C : Fma}{f : just 〈 S ∣ Γ 〉 ∣ [] ⊢L C}
  → sound (⊗l-1⋆ S Γ f) ≐ sound f
sound⊗l-1⋆ {just A} {[]} = refl
sound⊗l-1⋆ {just A} {B ∷ Γ} {f = f} =
  proof≐
  sound (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f))
  ≐⟨ sound⊗l-1 {f = ⊗l-1⋆ (just (A ⊗ B)) Γ f} ⟩
  sound (⊗l-1⋆ (just (A ⊗ B)) Γ f)
  ≐⟨ sound⊗l-1⋆ {S = just (A ⊗ B)}{Γ} ⟩
  sound f
  qed≐
sound⊗l-1⋆ {nothing} {[]}{f = f} = soundIl-1 {f = f}
sound⊗l-1⋆ {nothing} {B ∷ Γ}{f = f} =
  proof≐
  sound (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)))
  ≐⟨ soundIl-1 {f = ⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)} ⟩
  sound (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))
  ≐⟨ sound⊗l-1 {f = ⊗l-1⋆ (just (I ⊗ B)) Γ f} ⟩
  sound (⊗l-1⋆ (just (I ⊗ B)) Γ f)
  ≐⟨ sound⊗l-1⋆ {just (I ⊗ B)}{Γ} ⟩
  sound f
  qed≐

-- ====================================================================

-- sound is left inverse of strcmplt

soundstrcmplt : {S : Stp}{Γ : Cxt}{C : Fma}(f : 〈 S ∣ Γ 〉 ⇒ C) →
           sound (strcmplt {S}{Γ} f) ≐ f 
soundstrcmplt {S}{Γ} f =
  proof≐ 
  sound (strcmplt {S}{Γ} f)
  ≐⟨ sound⊗l-1⋆ {S}{Γ} ⟩
  sound (cmplt f)
  ≐⟨ soundcmplt f ⟩
  f
  qed≐
