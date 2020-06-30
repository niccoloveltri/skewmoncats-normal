{-# OPTIONS --rewriting #-}

module MulticatLaws where

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

-- ====================================================================

-- Extra laws satisfied by the cut rules (e.g. associativity, parallel
-- composition, etc.)

-- ====================================================================

-- an alternative representation of ⊗l-1

abstract
  ⊗l-1-alt : {Γ : Cxt}{A B C : Fma}(f : just (A ⊗ B) ∣ Γ ⊢ C)
    → ⊗l-1 f ≡ scut (⊗r ax (uf ax)) f
  ⊗l-1-alt ax = refl
  ⊗l-1-alt (⊗r {Γ = Γ}{Δ} f f') = cong₂ (⊗r {Γ = _ ∷ Γ}{Δ}) (⊗l-1-alt f) refl
  ⊗l-1-alt (⊗l f) = sym (ccut-unit [] f refl)
  ⊗l-1-alt (Ic Γ Δ f) = cong (Ic (_ ∷ Γ) Δ) (⊗l-1-alt f)
  ⊗l-1-alt (⊗c Γ Δ cJ cJ' f) = cong (⊗c (_ ∷ Γ) Δ cJ cJ') (⊗l-1-alt f)

-- ====================================================================

abstract

  scut⊗l-1 : {Γ Δ : Cxt} → {A B C D : Fma}
    → (f : just (A ⊗ B) ∣ Γ ⊢ C)(g : just C ∣ Δ ⊢ D)
    → ⊗l-1 (scut f g) ≡ scut (⊗l-1 f) g
  scut⊗l-1 ax g = ⊗l-1-alt g
  scut⊗l-1 (⊗r f f') ax = refl
  scut⊗l-1 (⊗r {Γ = Γ} {Δ} f f') (⊗r {Γ = Γ₁} {Δ₁} g g') = 
    cong₂ (⊗r {Γ = _ ∷ Γ ++ Δ ++ Γ₁}{Δ₁}) (scut⊗l-1 (⊗r f f') g) refl
  scut⊗l-1 {B = B} (⊗r {Γ = Γ} f f') (⊗l g) = scut⊗l-1 f (ccut [] f' g refl)
  scut⊗l-1 (⊗r {Γ = Γ} {Δ} f f') (Ic Γ' Δ' g) = cong (Ic (_ ∷ Γ ++ Δ ++ Γ') Δ') (scut⊗l-1 (⊗r f f') g)
  scut⊗l-1 (⊗r {Γ = Γ} {Δ} f f') (⊗c Γ' Δ' cJ cJ' g) = cong (⊗c (_ ∷ Γ ++ Δ ++ Γ') Δ' cJ cJ') (scut⊗l-1 (⊗r f f') g)
  scut⊗l-1 (⊗l f) g = refl
  scut⊗l-1 {Δ = Δ₁} (Ic Γ Δ f) g = cong (Ic (_ ∷ Γ) (Δ ++ Δ₁)) (scut⊗l-1 f g)
  scut⊗l-1 {Δ = Δ₁} (⊗c Γ Δ cJ cJ' f) g = cong (⊗c (_ ∷ Γ) (Δ ++ Δ₁) cJ cJ') (scut⊗l-1 f g)

-- ====================================================================


abstract
  scut⊗r-letI : ∀{S T Γ₁ Δ₁ Γ₂ Γ Δ A B C}
    → (f₁ : T ∣ Γ₁ ⊢ A) (f₃ : nothing ∣ Δ₁ ⊢ B) (f₂ : S ∣ Γ₂ ⊢ I) (g  : just (A ⊗ B) ∣ Γ ++ Δ ⊢ C)
    → scut (⊗r f₁ f₃) (letI Γ Δ f₂ g) ≡  letI (Γ₁ ++ Δ₁ ++ Γ) Δ f₂ (scut (⊗r f₁ f₃) g)
  scut⊗r-letI f₁ f₃ (uf f₂) g = scut⊗r-letI f₁ f₃ f₂ g
  scut⊗r-letI f₁ f₃ Ir g = refl
  scut⊗r-letI {S}{Γ₁ = Γ₁} {Δ₁} {Γ = Γ₂} {Δ₂} f₁ f₃ (Ic Γ Δ f₂) g =
    cong (Ic (Γ₁ ++ Δ₁ ++ Γ₂ ++ asCxt S Γ) (Δ ++ Δ₂)) (scut⊗r-letI f₁ f₃ f₂ g)
  scut⊗r-letI {S} {Γ₁ = Γ₁} {Δ₁} {Γ = Γ₂} {Δ₂} f₁ f₃ (⊗c Γ Δ cJ cJ' f₂) g =
    cong (⊗c (Γ₁ ++ Δ₁ ++ Γ₂ ++ asCxt S Γ) (Δ ++ Δ₂) cJ cJ') (scut⊗r-letI f₁ f₃ f₂ g)
  scut⊗r-letI f₁ f₃ ax g = refl
  scut⊗r-letI {Γ₁ = Γ₁} {Δ₁} {Γ₂} {Γ}{Δ} f₁ f₃ (Il f₂) g =
    cong (Ic (Γ₁ ++ Δ₁ ++ Γ) (Γ₂ ++ Δ)) (scut⊗r-letI f₁ f₃ f₂ g)
  scut⊗r-letI {Γ₁ = Γ₁} {Δ₁} {Γ₂} {Γ} {Δ} f₁ f₃ (⊗l f₂) g =
    cong (⊗c (Γ₁ ++ Δ₁ ++ Γ) (Γ₂ ++ Δ) _ _) (scut⊗r-letI f₁ f₃ f₂ g)


  letI-par-ccut1 : ∀ {S₁ S₂ T Γ₁ Γ₂} Δ₀ {Δ₁ Δ₂ A C} 
    → (f₁ : S₁ ∣ Γ₁ ⊢ I)(f₂ : S₂ ∣ Γ₂ ⊢ A)(g : T ∣ Δ₀ ++ Δ₁ ++ A ∷ Δ₂ ⊢ C)
    → letI Δ₀ (Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) f₁ (ccut (Δ₀ ++ Δ₁) f₂ g refl)
           ≡ ccut (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) f₂ (letI Δ₀ (Δ₁ ++ A ∷ Δ₂) f₁ g) refl
  letI-par-ccut1 Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} ax f₂ g 
    rewrite cases++-inj₂ (I ∷ Δ₁) Δ₀ Δ₂ A = refl
  letI-par-ccut1 Δ₀ (uf f₁) f₂ g = letI-par-ccut1 Δ₀ f₁ f₂ g
  letI-par-ccut1 Δ₀ Ir f₂ g = refl
  letI-par-ccut1 {_}{S₂} {Γ₁ = Γ₁}{Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} (Il f₁) f₂ g
    rewrite cases++-inj₂ (I ∷ Γ₁ ++ Δ₁) Δ₀ Δ₂ A =
    cong (Ic Δ₀ (Γ₁ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂)) (letI-par-ccut1 Δ₀ f₁ f₂ g)
  letI-par-ccut1 {_}{S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} (⊗l {A = A₁} {B} f₁) f₂ g 
    rewrite cases++-inj₂ (A₁ ⊗ B ∷ Γ₁ ++ Δ₁) Δ₀ Δ₂ A =
    cong (⊗c Δ₀ (Γ₁ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) _ _) (letI-par-ccut1 Δ₀ f₁ f₂ g)
  letI-par-ccut1 {S₁}{S₂} {Γ₂ = Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} (Ic Γ Δ f₁) f₂ g
    rewrite cases++-inj₂ (I ∷ Δ ++ Δ₁) (Δ₀ ++ asCxt S₁ Γ) Δ₂ A =
    cong (Ic (Δ₀ ++ asCxt S₁ Γ) (Δ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂)) (letI-par-ccut1 Δ₀ f₁ f₂ g)
  letI-par-ccut1 {S₁} {S₂} {Γ₂ = Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} (⊗c Γ Δ {J} {J'} cJ cJ' f₁) f₂ g
    rewrite cases++-inj₂ (J ⊗ J' ∷ Δ ++ Δ₁) (Δ₀ ++ asCxt S₁ Γ) Δ₂ A =
    cong (⊗c (Δ₀ ++ asCxt S₁ Γ) (Δ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) cJ cJ') (letI-par-ccut1 Δ₀ f₁ f₂ g)

  letI-par-ccut2 : ∀ {S₁ S₂ T Γ₁ Γ₂} Δ₀ {Δ₁ Δ₂ A C}
    → (f₁ : S₁ ∣ Γ₁ ⊢ A)(f₂ : S₂ ∣ Γ₂ ⊢ I)(g : T ∣ Δ₀ ++ A ∷ Δ₁ ++ Δ₂ ⊢ C)
    → letI (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) Δ₂ f₂ (ccut Δ₀ f₁ g refl)
           ≡ ccut Δ₀ f₁ (letI (Δ₀ ++ A ∷ Δ₁) Δ₂ f₂ g) refl
  letI-par-ccut2 Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} f₁ ax g
    rewrite cases++-inj₁ Δ₀ Δ₁ (I ∷ Δ₂) A = refl
  letI-par-ccut2 Δ₀ f₁ (uf f₂) g = letI-par-ccut2 Δ₀ f₁ f₂ g
  letI-par-ccut2 Δ₀ f₁ Ir g = refl
  letI-par-ccut2 {S₁} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} f₁ (Il f₂) g
    rewrite cases++-inj₁ Δ₀ Δ₁ (I ∷ Γ₂ ++ Δ₂) A =
    cong (Ic (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) (Γ₂ ++ Δ₂)) (letI-par-ccut2 Δ₀ f₁ f₂ g)
  letI-par-ccut2 {S₁} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} f₁ (⊗l {A = A₁} {B} f₂) g
    rewrite cases++-inj₁ Δ₀ Δ₁ (A₁ ⊗ B ∷ Γ₂ ++ Δ₂) A =
    cong (⊗c (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) (Γ₂ ++ Δ₂) _ _) (letI-par-ccut2 Δ₀ f₁ f₂ g)
  letI-par-ccut2 {S₁} {S₂} {Γ₁ = Γ₁} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} f₁ (Ic Γ Δ f₂) g
    rewrite cases++-inj₁ Δ₀ (Δ₁ ++ asCxt S₂ Γ) (I ∷ Δ ++ Δ₂) A =
    cong (Ic (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁ ++ asCxt S₂ Γ) (Δ ++ Δ₂)) (letI-par-ccut2 Δ₀ f₁ f₂ g)
  letI-par-ccut2 {S₁} {S₂} {Γ₁ = Γ₁} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} f₁ (⊗c Γ Δ {J} {J'} cJ cJ' f₂) g
    rewrite cases++-inj₁ Δ₀ (Δ₁ ++ asCxt S₂ Γ) (J ⊗ J' ∷ Δ ++ Δ₂) A =
    cong (⊗c (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁ ++ asCxt S₂ Γ) (Δ ++ Δ₂) cJ cJ') (letI-par-ccut2 Δ₀ f₁ f₂ g)

abstract
  mutual
    scut-par-ccut : {S T : Stp}{Γ₁ Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₂ C : Fma}
      → (f₁ : T ∣ Γ₁ ⊢ A₁)(f₂ : S ∣ Γ₂ ⊢ A₂)(g : just A₁ ∣ Δ ⊢ C)
      → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
      → scut f₁ (ccut Δ₀ f₂ g r) ≡ ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_++_ Γ₁) r)
    scut-par-ccut Δ₀ ax f₂ g refl = refl
    scut-par-ccut Δ₀ (uf f₁) f₂ g refl = cong uf (scut-par-ccut Δ₀ f₁ f₂ g refl)
    scut-par-ccut Δ₀ Ir f₂ g refl =
      begin
      scut Ir (ccut Δ₀ f₂ g refl)
      ≡⟨ sym (Il-1-scutIr (ccut Δ₀ f₂ g refl)) ⟩
      Il-1 (ccut Δ₀ f₂ g refl)
      ≡⟨ ccut-Il-1 Δ₀ f₂ g refl ⟩
      ccut Δ₀ f₂ (Il-1 g) refl
      ≡⟨ cong (λ x → ccut Δ₀ f₂ x refl) (Il-1-scutIr g) ⟩
      ccut Δ₀ f₂ (scut Ir g) refl
      ∎
    scut-par-ccut Δ₀ (⊗r f₁ f₃) f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
    scut-par-ccut Δ₀ {Δ'} (⊗r f₁ f₃) f₂ (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
    scut-par-ccut {S}{Γ₂ = Γ₂} Δ₀ {.(Γ₀ ++ Δ)} {A₂ = A₂} (⊗r {Γ = Γ} {Δ₁} f₁ f₃) f₂ (⊗r {Γ = .(Δ₀ ++ A₂ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ (Γ ++ Δ₁ ++ Δ₀) Γ₀ Δ A₂ =
      cong₂ (⊗r {Γ = Γ ++ Δ₁ ++ Δ₀ ++ asCxt S Γ₂ ++ Γ₀}{Δ}) (scut-par-ccut Δ₀ (⊗r f₁ f₃) f₂ g refl ) refl
    scut-par-ccut {Γ₂ = Γ₂} .(Γ ++ Γ₀) {Δ'} {A₂ = A₂} (⊗r {Γ = Γ₁} {Δ} f₁ f₃) f₂ (⊗r {Γ = Γ} {.(Γ₀ ++ A₂ ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl)
      rewrite cases++-inj₂ Γ₀ (Γ₁ ++ Δ ++ Γ) Δ' A₂ = refl
    scut-par-ccut Δ₀ (⊗r {Γ = Γ}{Δ} f₁ f₁') f₂ (⊗l {B = B} g) refl =
      begin
      scut f₁ (ccut [] f₁' (ccut (B ∷ Δ₀) f₂ g refl) refl)
      ≡⟨ cong (scut f₁) (ccut-par-ccut [] f₁' f₂ g refl) ⟩ 
      scut f₁ (ccut (Δ ++ Δ₀) f₂ (ccut [] f₁' g refl) refl)
      ≡⟨ scut-par-ccut (Δ ++ Δ₀) f₁ f₂ (ccut [] f₁' g refl) refl ⟩
       ccut (Γ ++ Δ ++ Δ₀) f₂ (scut f₁ (ccut [] f₁' g refl)) refl
      ∎
    scut-par-ccut Δ₀ {Δ'} (⊗r f₁ f₃) f₂ (Ic Γ Δ g) r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    scut-par-ccut {S} {Γ₂ = Γ₂} Δ₀ {.(Γ₀ ++ I ∷ Δ)} {A₂ = A₂} (⊗r {Γ = Γ} {Δ₁} f₁ f₃) f₂ (Ic .(Δ₀ ++ A₂ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ (Γ ++ Δ₁ ++ Δ₀) Γ₀ (I ∷ Δ) A₂ = cong (Ic (Γ ++ Δ₁ ++ Δ₀ ++ asCxt S Γ₂  ++ Γ₀) Δ) (scut-par-ccut Δ₀ (⊗r f₁ f₃) f₂ g refl)
    scut-par-ccut {Γ₂ = Γ₂} .Γ {.Δ} (⊗r {Γ = Γ₁} {Δ₁} f₁ f₃) f₂ (Ic Γ Δ g) refl | inj₂ ([] , refl , refl) 
      rewrite cases++-inj₂ [] (Γ₁ ++ Δ₁ ++ Γ) Δ I = scut⊗r-letI f₁ f₃ f₂ g
    scut-par-ccut {S} {Γ₂ = Γ₂} .(Γ ++ I ∷ Γ₀) {Δ'} {A₂ = A₂} (⊗r {Γ = Γ₁} {Δ} f₁ f₃) f₂ (Ic Γ .(Γ₀ ++ A₂ ∷ Δ') g) refl | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀) (Γ₁ ++ Δ ++ Γ) Δ' A₂ = cong (Ic (Γ₁ ++ Δ ++ Γ) (Γ₀ ++ asCxt S Γ₂ ++ Δ')) (scut-par-ccut (Γ ++ Γ₀) (⊗r f₁ f₃) f₂ g refl)
    scut-par-ccut Δ₀ {Δ'} (⊗r f₁ f₃) f₂ (⊗c Γ Δ {J}{J'} cJ cJ' g) r with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) r
    scut-par-ccut {S}{Γ₂ = Γ₂} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} {A₂ = A₂} (⊗r {Γ = Γ} {Δ₁} f₁ f₃) f₂ (⊗c .(Δ₀ ++ A₂ ∷ Γ₀) Δ {J}{J'} cJ cJ' g) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ (Γ ++ Δ₁ ++ Δ₀) Γ₀ (J ⊗ J' ∷ Δ) A₂ = cong (⊗c (Γ ++ Δ₁ ++ Δ₀ ++ asCxt S Γ₂ ++ Γ₀) Δ cJ cJ') (scut-par-ccut Δ₀ (⊗r f₁ f₃) f₂ g refl)
    scut-par-ccut {Γ₂ = Γ₂} .Γ {.Δ} (⊗r {Γ = Γ₁} {Δ₁} f₁ f₃) f₂ (⊗c Γ Δ {J}{J'} cJ cJ' g) refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] (Γ₁ ++ Δ₁ ++ Γ) Δ (J ⊗ J') = scut⊗r-let⊗ f₁ f₃ f₂ g 
    scut-par-ccut {S}{Γ₂ = Γ₂} .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} {A₂ = A₂} (⊗r {Γ = Γ₁} {Δ} f₁ f₃) f₂ (⊗c Γ .(Γ₀ ++ A₂ ∷ Δ') {J}{J'} cJ cJ' g) refl | inj₂ (._ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Γ₁ ++ Δ ++ Γ) Δ' A₂ = cong (⊗c (Γ₁ ++ Δ ++ Γ) (Γ₀ ++ asCxt S Γ₂ ++ Δ') cJ cJ') (scut-par-ccut (Γ ++ J ∷ J' ∷ Γ₀) (⊗r f₁ f₃) f₂ g refl)
    scut-par-ccut {S} {Γ₂ = Γ₂} Δ₀ {Δ'} {A₂ = A₂} (Ic Γ Δ f₁) f₂ g refl
      rewrite cases++-inj₂ (I ∷ Δ ++ Δ₀) Γ Δ' A₂ = cong (Ic Γ (Δ ++ Δ₀ ++ asCxt S Γ₂ ++ Δ')) (scut-par-ccut Δ₀ f₁ f₂ g refl)
    scut-par-ccut {S}{Γ₂ = Γ₂} Δ₀ {Δ'} {A₂ = A₂} (⊗c Γ Δ {J} {J'} cJ cJ' f₁) f₂ g refl
      rewrite cases++-inj₂ (J ⊗ J' ∷ Δ ++ Δ₀) Γ Δ' A₂ = cong (⊗c Γ (Δ ++ Δ₀ ++ asCxt S Γ₂ ++ Δ') cJ cJ') (scut-par-ccut Δ₀ f₁ f₂ g refl)
    scut-par-ccut Δ₀ (Il f₁) f₂ g refl = cong Il (scut-par-ccut Δ₀ f₁ f₂ g refl)
    scut-par-ccut Δ₀ (⊗l f₁) f₂ g refl = cong ⊗l (scut-par-ccut Δ₀ f₁ f₂ g refl)

    scut⊗r-let⊗ : ∀{S T Γ₁ Δ₁ Γ₂ Γ Δ A B C J J'}{cJ : isCl J}{cJ' : isCl J'}
      → (f₁ : T ∣ Γ₁ ⊢ A) (f₃ : nothing ∣ Δ₁ ⊢ B) (f₂ : S ∣ Γ₂ ⊢ J ⊗ J') (g  : just (A ⊗ B) ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C)
      → scut (⊗r f₁ f₃) (let⊗ Γ Δ cJ cJ' f₂ g) ≡  let⊗ (Γ₁ ++ Δ₁ ++ Γ) Δ cJ cJ' f₂ (scut (⊗r f₁ f₃) g)
    scut⊗r-let⊗ f₁ f₃ (uf f₂) g = scut⊗r-let⊗ f₁ f₃ f₂ g
    scut⊗r-let⊗ {S} {Γ₁ = Γ₁} {Δ₁} {Γ = Γ₂} {Δ₂} f₁ f₃ (Ic Γ Δ f₂) g =
      cong (Ic (Γ₁ ++ Δ₁ ++ Γ₂ ++ asCxt S Γ) (Δ ++ Δ₂)) (scut⊗r-let⊗ f₁ f₃ f₂ g)
    scut⊗r-let⊗ {S} {Γ₁ = Γ₁} {Δ₁} {Γ = Γ₂} {Δ₂} f₁ f₃ (⊗c Γ Δ cJ cJ' f₂) g =
      cong (⊗c (Γ₁ ++ Δ₁ ++ Γ₂ ++ asCxt S Γ) (Δ ++ Δ₂) cJ cJ') (scut⊗r-let⊗ f₁ f₃ f₂ g)
    scut⊗r-let⊗ f₁ f₃ ax g = refl
    scut⊗r-let⊗ {Γ₁ = Γ₁}{Δ₁}{Γ = Γ} f₁ f₃ (⊗r f₂ f₂') g =
      trans (scut-par-ccut Γ (⊗r f₁ f₃) f₂ (ccut (Γ ++ _ ∷ []) f₂' g refl) refl)
        (cong (λ x → ccut (Γ₁ ++ Δ₁ ++ Γ) f₂ x refl) (scut-par-ccut (Γ ++ _ ∷ []) (⊗r f₁ f₃) f₂' g refl))
    scut⊗r-let⊗ {Γ₁ = Γ₁} {Δ₁} {Γ₂} {Γ}{Δ} f₁ f₃ (Il f₂) g =
      cong (Ic (Γ₁ ++ Δ₁ ++ Γ) (Γ₂ ++ Δ)) (scut⊗r-let⊗ f₁ f₃ f₂ g)
    scut⊗r-let⊗ {Γ₁ = Γ₁} {Δ₁} {Γ₂} {Γ} {Δ} f₁ f₃ (⊗l f₂) g =
      cong (⊗c (Γ₁ ++ Δ₁ ++ Γ) (Γ₂ ++ Δ) _ _) (scut⊗r-let⊗ f₁ f₃ f₂ g)

    ccut-par-ccut : {S₁ S₂ T : Stp} → {Γ₁ Γ₂ : Cxt} → (Δ₀ : Cxt) → {Δ Δ₁ Δ₂ : Cxt} → {A₁ A₂ C : Fma}
      → (f₁ : S₁ ∣ Γ₁ ⊢ A₁)(f₂ : S₂ ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
      → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
      → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) refl ≡ ccut (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) f₂ (ccut Δ₀ f₁ g r) refl
    ccut-par-ccut Δ₀ f₁ f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-par-ccut Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (uf g) r with cases∷ (Δ₀ ++ A₁ ∷ Δ₁) r
    ccut-par-ccut Δ₀ f₁ f₂ (uf g) r | inj₁ (p , q , s) = ⊥-elim ([]disj∷ Δ₀ (sym q))
    ccut-par-ccut Δ₀ f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , s) with cases∷ Δ₀ r
    ccut-par-ccut {nothing} .[] {.(_ ∷ Γ₀ ++ _ ∷ _)} {_} {_} {_} f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = scut-par-ccut Γ₀ f₁ f₂ g refl
    ccut-par-ccut {just x} .[] {.(_ ∷ Γ₀ ++ _ ∷ _)} {_} {_} {_} f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = cong uf (scut-par-ccut Γ₀ f₁ f₂ g refl) 
    ccut-par-ccut .(_ ∷ Δ₀) f₁ f₂ (uf g) r | inj₂ (._ , refl , refl) | inj₂ (Δ₀ , refl , refl) = cong uf (ccut-par-ccut Δ₀ f₁ f₂ g refl)
    ccut-par-ccut Δ₀ f₁ f₂ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ Δ r
    ccut-par-ccut {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀ ++ Δ)} {A₁} {A₂} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) Δ A₁ | cases++-inj₁ Δ₀ (Δ₁ ++ asCxt S₂ Γ₂ ++ Γ₀) Δ A₁ | cases++-inj₁ (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) Γ₀ Δ A₂ =
      cong₂ (⊗r {Γ = Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Γ₀}{Δ}) (ccut-par-ccut Δ₀ f₁ f₂ g refl) refl
    ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ₂)} g g₁) r | inj₂ (Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym q)
    ccut-par-ccut {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = ._} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r g g₁) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ asCxt S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ Γ₀ (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀') Δ₂ A₂ = refl
    ccut-par-ccut {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} ._ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁) refl | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , refl , refl)
      rewrite cases++-inj₂ Γ₀' Γ (Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₂ Γ₀' Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (Γ₀' ++ asCxt S₁ Γ₁ ++ Δ₁) Γ Δ₂ A₂ =
      cong (⊗r g) (ccut-par-ccut Γ₀' f₁ f₂ g₁ refl)
    ccut-par-ccut Δ₀ f₁ f₂ (Il g) refl = cong Il (ccut-par-ccut Δ₀ f₁ f₂ g refl)
    ccut-par-ccut Δ₀ f₁ f₂ (⊗l {B = B} g) refl = cong ⊗l (ccut-par-ccut (B ∷ Δ₀) f₁ f₂ g refl)
    ccut-par-ccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (Ic Γ Δ g) r with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ (I ∷ Δ) r
    ccut-par-ccut {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀ ++ I ∷ Δ)} {A₁} {A₂} f₁ f₂ (Ic .(Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Δ₁ ++ asCxt S₂ Γ₂ ++ Γ₀) (I ∷ Δ) A₁ | cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) (I ∷ Δ) A₁ | cases++-inj₁ (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) Γ₀ (I ∷ Δ) A₂ =
      cong (Ic (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Γ₀) Δ) (ccut-par-ccut Δ₀ f₁ f₂ g refl)
    ccut-par-ccut {S₁}{S₂}{Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.Δ} {A₁} {.I} f₁ f₂ (Ic .(Δ₀ ++ A₁ ∷ Δ₁) Δ g) refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₁ Δ₀ Δ₁ (I ∷ Δ) A₁ | cases++-inj₂ [] (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) Δ I = sym (letI-par-ccut2 Δ₀ f₁ f₂ g)
    ccut-par-ccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (Ic Γ .(Γ₀ ++ A₂ ∷ Δ₂) g) r | inj₂ (.I ∷ Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ (I ∷ Γ₀) (sym q)
    ccut-par-ccut {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .(Γ₀' ++ I ∷ Γ₀)} {Δ₂} {A₁} {A₂} f₁ f₂ (Ic ._ ._ g) refl | inj₂ (.I ∷ Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (I ∷ Γ₀ ++ asCxt S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₁ Δ₀ Γ₀' (I ∷ Γ₀ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (I ∷ Γ₀) (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀') Δ₂ A₂ =
      cong (Ic (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀') (Γ₀ ++ asCxt S₂ Γ₂ ++ Δ₂)) (ccut-par-ccut {Γ₁ = Γ₁} Δ₀ {Δ₁ = Γ₀' ++ Γ₀} f₁ f₂ g refl)
    ccut-par-ccut {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} .Γ {Δ₁ = .Γ₀} {Δ₂} {.I} {A₂} f₁ f₂ (Ic Γ .(Γ₀ ++ A₂ ∷ Δ₂) g) refl | inj₂ (.I ∷ Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Γ (Γ₀ ++ asCxt S₂ Γ₂ ++ Δ₂) I | cases++-inj₂ [] Γ (Γ₀ ++ A₂ ∷ Δ₂) I = letI-par-ccut1 Γ f₁ f₂ g
    ccut-par-ccut {S₁}{S₂}{Γ₁ = Γ₁} {Γ₂} ._ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (Ic Γ ._ g) refl | inj₂ (.I ∷ ._ , refl , refl) | inj₂ (.I ∷ Γ₀' , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀') Γ (Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₂ (I ∷ Γ₀') Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (I ∷ Γ₀' ++ asCxt S₁ Γ₁ ++ Δ₁)  Γ Δ₂ A₂ =
      cong (Ic Γ (Γ₀' ++ asCxt S₁ Γ₁ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂)) (ccut-par-ccut (Γ ++ Γ₀') f₁ f₂ g refl)
    ccut-par-ccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗c Γ Δ {J} {J'} cJ cJ' g) r with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ (J ⊗ J' ∷ Δ) r
    ccut-par-ccut {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀ ++ J ⊗ J' ∷ Δ)} {A₁} {A₂} f₁ f₂ (⊗c .(Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀) Δ {J} {J'} cJ cJ' g) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Δ₁ ++ asCxt S₂ Γ₂ ++ Γ₀) (J ⊗ J' ∷ Δ) A₁ | cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) (J ⊗ J' ∷ Δ) A₁ | cases++-inj₁ (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) Γ₀ (J ⊗ J' ∷ Δ) A₂ =
      cong (⊗c (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Γ₀) Δ cJ cJ') (ccut-par-ccut Δ₀ f₁ f₂ g refl)
    ccut-par-ccut {S₁}{S₂}{Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.Δ} {A₁} {.(J ⊗ J')} f₁ f₂ (⊗c .(Δ₀ ++ A₁ ∷ Δ₁) Δ {J} {J'} cJ cJ' g) refl | inj₂ ([] , refl , refl) 
      rewrite cases++-inj₁ Δ₀ Δ₁ (J ⊗ J' ∷ Δ) A₁ | cases++-inj₂ [] (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) Δ (J ⊗ J') = sym (let⊗-par-ccut2 Δ₀ f₁ f₂ g)
    ccut-par-ccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗c Γ .(Γ₀ ++ A₂ ∷ Δ₂) {J} {J'} cJ cJ' g) r | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ (_ ∷ Γ₀) (sym q)
    ccut-par-ccut {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = ._} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗c ._ ._ {J} {J'} cJ cJ' g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Γ₀ ++ asCxt S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Γ₀ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀') Δ₂ A₂
      = cong (⊗c (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀') (Γ₀ ++ asCxt S₂ Γ₂ ++ Δ₂) cJ cJ') (ccut-par-ccut {Γ₁ = Γ₁} Δ₀ {Δ₁ = Γ₀' ++ J ∷ J' ∷ Γ₀} f₁ f₂ g refl)
    ccut-par-ccut {S₁}{S₂}{Γ₁ = Γ₁} {Γ₂} .Γ {Δ₁ = .Γ₀} {Δ₂} {.(J ⊗ J')} {A₂} f₁ f₂ (⊗c Γ ._ {J} {J'} cJ cJ' g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Γ (Γ₀ ++ asCxt S₂ Γ₂ ++ Δ₂) (J ⊗ J') | cases++-inj₂ [] Γ (Γ₀ ++ A₂ ∷ Δ₂) (J ⊗ J') = let⊗-par-ccut1 Γ f₁ f₂ g
    ccut-par-ccut {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} ._ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗c Γ ._ {J} {J'} cJ cJ' g) refl | inj₂ (.(J ⊗ J') ∷ ._ , refl , refl) | inj₂ (.(J ⊗ J') ∷ Γ₀' , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (J ⊗ J' ∷ Γ₀' ++ asCxt S₁ Γ₁ ++ Δ₁)  Γ Δ₂ A₂ =
      cong (⊗c Γ (Γ₀' ++ asCxt S₁ Γ₁ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) cJ cJ') (ccut-par-ccut (Γ ++ J ∷ J' ∷ Γ₀') f₁ f₂ g refl)

    let⊗-par-ccut1 : ∀ {S₁ S₂ T Γ₁ Γ₂} Δ₀ {Δ₁ Δ₂ A C J J'} {cJ : isCl J}{cJ' : isCl J'}
      → (f₁ : S₁ ∣ Γ₁ ⊢ J ⊗ J')(f₂ : S₂ ∣ Γ₂ ⊢ A)(g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ++ A ∷ Δ₂ ⊢ C)
      → let⊗ Δ₀ (Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) cJ cJ' f₁ (ccut (Δ₀ ++ J ∷ J' ∷ Δ₁) f₂ g refl)
             ≡ ccut (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) f₂ (let⊗ Δ₀ (Δ₁ ++ A ∷ Δ₂) cJ cJ' f₁ g) refl
    let⊗-par-ccut1 Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} {J = J} {J'} ax f₂ g
      rewrite cases++-inj₂ (J ⊗ J' ∷ Δ₁) Δ₀ Δ₂ A = refl
    let⊗-par-ccut1 Δ₀ (uf f₁) f₂ g = let⊗-par-ccut1 Δ₀ f₁ f₂ g
    let⊗-par-ccut1 Δ₀ {Δ₁} (⊗r {Δ = Δ} f₁ f₃) f₂ g =
      trans (cong (λ x → ccut Δ₀ f₁ x refl) (ccut-par-ccut (Δ₀ ++ _ ∷ []) f₃ f₂ g refl))
        (ccut-par-ccut Δ₀ {_}{Δ ++ Δ₁} f₁ f₂ (ccut (Δ₀ ++ _ ∷ []) f₃ g refl) refl) 
    let⊗-par-ccut1 {S₂ = S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} (Il f₁) f₂ g
      rewrite cases++-inj₂ (I ∷ Γ₁ ++ Δ₁) Δ₀ Δ₂ A =
      cong (Ic Δ₀ (Γ₁ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂)) (let⊗-par-ccut1 Δ₀ f₁ f₂ g)
    let⊗-par-ccut1 {S₂ = S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁} {Δ₂} {A₁} {J = J} {J'} (⊗l {A = A} {B} f₁) f₂ g
      rewrite cases++-inj₂ (A ⊗ B ∷ Γ₁ ++ Δ₁) Δ₀ Δ₂ A₁ =
      cong (⊗c Δ₀ (Γ₁ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) _ _) (let⊗-par-ccut1 Δ₀ f₁ f₂ g)
    let⊗-par-ccut1 {S₁} {S₂} {Γ₂ = Γ₂} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} (Ic Γ Δ f₁) f₂ g
      rewrite cases++-inj₂ (I ∷ Δ ++ Δ₁) (Δ₀ ++ asCxt S₁ Γ) Δ₂ A =
      cong (Ic (Δ₀ ++ asCxt S₁ Γ) (Δ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂)) (let⊗-par-ccut1 Δ₀ f₁ f₂ g)
    let⊗-par-ccut1 {S₁} {S₂} {Γ₂ = Γ₂} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} (⊗c Γ Δ {J₁} {J''} cJ cJ' f₁) f₂ g
      rewrite cases++-inj₂ (J₁ ⊗ J'' ∷ Δ ++ Δ₁) (Δ₀ ++ asCxt S₁ Γ) Δ₂ A =
      cong (⊗c (Δ₀ ++ asCxt S₁ Γ) (Δ ++ Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) cJ cJ') (let⊗-par-ccut1 Δ₀ f₁ f₂ g)
 
    let⊗-par-ccut2 : ∀ {S₁ S₂ T Γ₁ Γ₂} Δ₀ {Δ₁ Δ₂ A C J J'} {cJ : isCl J}{cJ' : isCl J'}
      → (f₁ : S₁ ∣ Γ₁ ⊢ A)(f₂ : S₂ ∣ Γ₂ ⊢ J ⊗ J')(g : T ∣ Δ₀ ++ A ∷ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)
      → let⊗ (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) Δ₂ cJ cJ' f₂ (ccut Δ₀ f₁ g refl)
             ≡ ccut Δ₀ f₁ (let⊗ (Δ₀ ++ A ∷ Δ₁) Δ₂ cJ cJ' f₂ g) refl
    let⊗-par-ccut2 Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} f₁ ax g
      rewrite cases++-inj₁ Δ₀ Δ₁ (J ⊗ J' ∷ Δ₂) A = refl
    let⊗-par-ccut2 Δ₀ f₁ (uf f₂) g = let⊗-par-ccut2 Δ₀ f₁ f₂ g
    let⊗-par-ccut2 {S₁} {Γ₁ = Γ₁} Δ₀ {Δ₁} f₁ (⊗r f₂ f₃) g =
      trans (cong (λ x → ccut (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) f₂ x refl) (sym (ccut-par-ccut Δ₀ {_}{Δ₁ ++ _ ∷ []} f₁ f₃ g refl)))
        (sym (ccut-par-ccut Δ₀ f₁ f₂ (ccut (Δ₀ ++ _ ∷ Δ₁ ++ _ ∷ []) f₃ g refl) refl))
    let⊗-par-ccut2 {S₁} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} f₁ (Il f₂) g
      rewrite cases++-inj₁ Δ₀ Δ₁ (I ∷ Γ₂ ++ Δ₂) A =
      cong (Ic (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) (Γ₂ ++ Δ₂)) (let⊗-par-ccut2 Δ₀ f₁ f₂ g)
    let⊗-par-ccut2 {S₁} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} f₁ (⊗l {A = A₁} {B} f₂) g
      rewrite cases++-inj₁ Δ₀ Δ₁ (A₁ ⊗ B ∷ Γ₂ ++ Δ₂) A =
      cong (⊗c (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) (Γ₂ ++ Δ₂) _ _) (let⊗-par-ccut2 Δ₀ f₁ f₂ g)
    let⊗-par-ccut2 {S₁} {S₂} {Γ₁ = Γ₁} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} f₁ (Ic Γ Δ f₂) g
      rewrite cases++-inj₁ Δ₀ (Δ₁ ++ asCxt S₂ Γ) (I ∷ Δ ++ Δ₂) A =
      cong (Ic (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁ ++ asCxt S₂ Γ) (Δ ++ Δ₂)) (let⊗-par-ccut2 Δ₀ f₁ f₂ g)
    let⊗-par-ccut2 {S₁} {S₂} {Γ₁ = Γ₁} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} f₁ (⊗c Γ Δ {J₁} {J''} cJ cJ' f₂) g 
      rewrite cases++-inj₁ Δ₀ (Δ₁ ++ asCxt S₂ Γ) (J₁ ⊗ J'' ∷ Δ ++ Δ₂) A =
      cong (⊗c (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁ ++ asCxt S₂ Γ) (Δ ++ Δ₂) cJ cJ') (let⊗-par-ccut2 Δ₀ f₁ f₂ g)

  scut-letI : {S T : Stp} → {Γ : Cxt} (Γ₁ Γ₂ : Cxt) {Δ : Cxt} → {A C : Fma} → 
              (f : S ∣ Γ ⊢ I)  (g : T ∣ Γ₁ ++ Γ₂ ⊢ A) (h : just A ∣ Δ ⊢ C) →
              scut (letI Γ₁ Γ₂ f g) h ≡ letI Γ₁ (Γ₂ ++ Δ) f (scut g h)
  scut-letI Γ₁ Γ₂ ax g h = refl
  scut-letI Γ₁ Γ₂ (uf f) g h = scut-letI Γ₁ Γ₂ f g h
  scut-letI Γ₁ Γ₂ Ir g h = refl
  scut-letI {Γ = Γ} Γ₁ Γ₂ {Δ} (Il f) g h = cong (Ic Γ₁ (Γ ++ Γ₂ ++ Δ)) (scut-letI Γ₁ Γ₂ f g h)
  scut-letI {Γ = Γ} Γ₁ Γ₂ {Δ} (⊗l f) g h = cong (⊗c Γ₁ (Γ ++ Γ₂ ++ Δ) _ _) (scut-letI Γ₁ Γ₂ f g h)
  scut-letI {S} Γ₁ Γ₂ {Δ₁} (Ic Γ Δ f) g h = cong (Ic (Γ₁ ++ asCxt S Γ) (Δ ++ Γ₂ ++ Δ₁)) (scut-letI Γ₁ Γ₂ f g h)
  scut-letI {S} Γ₁ Γ₂ {Δ₁} (⊗c Γ Δ cJ cJ' f) g h = cong (⊗c (Γ₁ ++ asCxt S Γ) (Δ ++ Γ₂ ++ Δ₁) cJ cJ') (scut-letI Γ₁ Γ₂ f g h)

  letI-letI : {S₁ S₂ T : Stp} → {Γ : Cxt} → (Δ₁ Δ₂ Λ₁ Λ₂ : Cxt) → {C : Fma} → 
             (f : S₁ ∣ Γ ⊢ I) (g : S₂ ∣ Δ₁ ++ Δ₂ ⊢ I) (h : T ∣ Λ₁ ++ Λ₂ ⊢ C) → 
            letI (Λ₁ ++ asCxt S₂ Δ₁) (Δ₂ ++ Λ₂) f (letI Λ₁ Λ₂ g h)  ≡ letI Λ₁ Λ₂ (letI Δ₁ Δ₂ f g) h
  letI-letI Δ₁ Δ₂ Λ₁ Λ₂ ax g h = refl
  letI-letI Δ₁ Δ₂ Λ₁ Λ₂ (uf f) g h = letI-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h
  letI-letI Δ₁ Δ₂ Λ₁ Λ₂ Ir g h = refl
  letI-letI {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (Il f) g h =
    cong (Ic (Λ₁ ++ asCxt S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂)) (letI-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h)
  letI-letI {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (⊗l f) g h =
    cong (⊗c (Λ₁ ++ asCxt S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂) _ _) (letI-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h)
  letI-letI {S₁} {S₂} Δ₁ Δ₂ Λ₁ Λ₂ (Ic Γ Δ f) g h =
    cong (Ic (Λ₁ ++ asCxt S₂ Δ₁ ++ asCxt S₁ Γ) (Δ ++ Δ₂ ++ Λ₂)) (letI-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h)
  letI-letI {S₁} {S₂} Δ₁ Δ₂ Λ₁ Λ₂ (⊗c Γ Δ cJ cJ' f) g h = 
    cong (⊗c (Λ₁ ++ asCxt S₂ Δ₁ ++ asCxt S₁ Γ) (Δ ++ Δ₂ ++ Λ₂) _ _) (letI-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h)

  
  mutual
    let⊗-letI-s : {S T : Stp} → {Γ Δ : Cxt} → (Λ₁ Λ₂ : Cxt) → {C J J' : Fma} → {cJ : isCl J} {cJ' : isCl J'} → 
                (f : S ∣ Γ ⊢ J ⊗ J') (g : just J ∣ J' ∷ Δ ⊢ I) (h : T ∣ Λ₁ ++ Λ₂ ⊢ C) → 
                let⊗ Λ₁ (Δ ++ Λ₂) cJ cJ' f (letI Λ₁ Λ₂ g h) ≗ letI Λ₁ Λ₂ (let⊗ [] Δ cJ cJ' f (uf g)) h
    let⊗-letI-s Λ₁ Λ₂ ax g h = refl
    let⊗-letI-s Λ₁ Λ₂ (uf f) g h = let⊗-letI-s Λ₁ Λ₂ f g h
    let⊗-letI-s {nothing} {Δ} Λ₁ Λ₂ (⊗r {Γ = Γ} f f₁) g h =
      ≡-to-≗ (ccut-par-ccut Λ₁ f f₁ (letI Λ₁ Λ₂ g h) refl)
      ∙ cong-ccut2 (Λ₁ ++ Γ) {f = f₁} refl (ccut-letI-s Λ₁ Λ₂ f g h)
      ∙ ccut-letI Γ Λ₁ Λ₂ f₁ (scut f g) h refl
      ∙ ≡-to-≗ (cong (λ x → letI Λ₁ Λ₂ x h) (sym (scut-par-ccut [] f f₁ g refl)))
    let⊗-letI-s {just A} {Δ} Λ₁ Λ₂ (⊗r {Γ = Γ} f f₁) g h =
      ≡-to-≗ (ccut-par-ccut Λ₁ f f₁ (letI Λ₁ Λ₂ g h) refl)
      ∙ cong-ccut2 (Λ₁ ++ A ∷ Γ) {f = f₁} refl (ccut-letI-s Λ₁ Λ₂ f g h)
      ∙ ccut-letI Γ Λ₁ Λ₂ f₁ (scut f g) h refl
      ∙ ≡-to-≗ (cong (λ x → letI Λ₁ Λ₂ x h) (sym (scut-par-ccut [] f f₁ g refl)))
    let⊗-letI-s {Γ = Γ} {Δ} Λ₁ Λ₂ (Il f) g h =
      Ic Λ₁ (Γ ++ Δ ++ Λ₂) (let⊗-letI-s Λ₁ Λ₂ f g h)
    let⊗-letI-s {Γ = Γ} {Δ} Λ₁ Λ₂ (⊗l f) g h = 
      ⊗c Λ₁ (Γ ++ Δ ++ Λ₂) _ _ (let⊗-letI-s Λ₁ Λ₂ f g h)
    let⊗-letI-s {S} {Δ = Δ₁} Λ₁ Λ₂ (Ic Γ Δ f) g h =
      Ic (Λ₁ ++ asCxt S Γ) (Δ ++ Δ₁ ++ Λ₂) (let⊗-letI-s Λ₁ Λ₂ f g h)
    let⊗-letI-s {S} {Δ = Δ₁} Λ₁ Λ₂ (⊗c Γ Δ cJ cJ' f) g h = 
      ⊗c (Λ₁ ++ asCxt S Γ) (Δ ++ Δ₁ ++ Λ₂) _ _ (let⊗-letI-s Λ₁ Λ₂ f g h)
    
    let⊗-letI : {S₁ S₂ T : Stp} → {Γ : Cxt} → (Δ₁ Δ₂ Λ₁ Λ₂ : Cxt) → {C J J' : Fma} → {cJ : isCl J} {cJ' : isCl J'} → 
              (f : S₁ ∣ Γ ⊢ J ⊗ J') (g : S₂ ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ I) (h : T ∣ Λ₁ ++ Λ₂ ⊢ C) → 
              let⊗ (Λ₁ ++ asCxt S₂ Δ₁) (Δ₂ ++ Λ₂) cJ cJ' f (letI Λ₁ Λ₂ g h) ≗ letI Λ₁ Λ₂ (let⊗ Δ₁ Δ₂ cJ cJ' f g) h
    let⊗-letI Δ₁ Δ₂ Λ₁ Λ₂ ax g h = refl
    let⊗-letI Δ₁ Δ₂ Λ₁ Λ₂ (uf f) g h = let⊗-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h
    let⊗-letI {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (⊗r f f') g h =
      cong-ccut2 (Λ₁ ++ asCxt S₂ Δ₁) {f = f} refl (ccut-letI (Δ₁ ++ _ ∷ [])  Λ₁ Λ₂ f' g h refl)
      ∙ ccut-letI Δ₁ Λ₁ Λ₂ f (ccut (Δ₁ ++ _ ∷ []) f' g refl) h refl
    let⊗-letI {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (Il f) g h =
      Ic (Λ₁ ++ asCxt S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂) (let⊗-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h)
    let⊗-letI {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (⊗l f) g h =
      ⊗c (Λ₁ ++ asCxt S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂) _ _ (let⊗-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h)
    let⊗-letI {S₁} {S₂} Δ₁ Δ₂ Λ₁ Λ₂ (Ic Γ Δ f) g h =
      Ic (Λ₁ ++ asCxt S₂ Δ₁ ++ asCxt S₁ Γ) (Δ ++ Δ₂ ++ Λ₂) (let⊗-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h)
    let⊗-letI {S₁} {S₂} Δ₁ Δ₂ Λ₁ Λ₂ (⊗c Γ Δ cJ cJ' f) g h = 
      ⊗c (Λ₁ ++ asCxt S₂ Δ₁ ++ asCxt S₁ Γ) (Δ ++ Δ₂ ++ Λ₂) _ _ (let⊗-letI Δ₁ Δ₂ Λ₁ Λ₂ f g h)



    ccut-letI-s : {S₁ T : Stp} → {Γ Δ : Cxt} → (Λ₁ Λ₂ : Cxt) → {A C : Fma} → 
                (f : S₁ ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ I) (h : T ∣ Λ₁ ++ Λ₂ ⊢ C) → 
                ccut Λ₁ f (letI Λ₁ Λ₂ g h) refl ≗ letI Λ₁ Λ₂ (scut f g) h
    ccut-letI-s Λ₁ Λ₂ f ax h rewrite cases++-inj₂ [] Λ₁ Λ₂ I = ≡-to-≗ (cong (λ x → letI Λ₁ Λ₂ x h) (sym (scut-unit f)))
    ccut-letI-s {nothing}{Δ = Δ} Λ₁ Λ₂ f (Il g) h
      rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂) I = ≡-to-≗ (letI-letI [] Δ Λ₁ Λ₂ f g h) ∙ cong-letI1 Λ₁ Λ₂ h (letI-[] Δ f g)
    ccut-letI-s {just _}{Δ = Δ} Λ₁ Λ₂ f (Il g) h
      rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂) I = ≡-to-≗ (letI-letI [] Δ Λ₁ Λ₂ f g h) ∙ cong-letI1 Λ₁ Λ₂ h (letI-[]-j Δ f g)
    ccut-letI-s {nothing} {Δ = Δ} Λ₁ Λ₂ f (⊗l {A = A} {B} g) h
      rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂)  (A ⊗ B) = let⊗-letI-s Λ₁ Λ₂ f g h ∙ cong-letI1 Λ₁ Λ₂ h (let⊗-[] Δ f g) 
    ccut-letI-s {just _} {Δ = Δ} Λ₁ Λ₂ f (⊗l {A = A} {B} g) h
      rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂)  (A ⊗ B) = let⊗-letI-s Λ₁ Λ₂ f g h ∙ cong-letI1 Λ₁ Λ₂ h (let⊗-[]-j Δ f g) 
    ccut-letI-s {S₁}{Γ = Γ₁} Λ₁ Λ₂ {A} f (Ic Γ Δ g) h
      rewrite cases++-inj₁ Λ₁ Γ (Δ ++ Λ₂) A | cases++-inj₁ Λ₁ Γ (I ∷ Δ ++ Λ₂) A =
      Ic (Λ₁ ++ asCxt S₁ Γ₁ ++ Γ) (Δ ++ Λ₂) (ccut-letI-s Λ₁ Λ₂ f g h)
      ∙ cong-letI1 Λ₁ Λ₂ h (~ scut-Ic Γ Δ f g) 
    ccut-letI-s {S₁}{Γ = Γ₁} Λ₁ Λ₂ {A} f (⊗c Γ Δ {J = J}{J'} _ _ g) h
      rewrite cases++-inj₁ Λ₁ Γ (Δ ++ Λ₂) A | cases++-inj₁ Λ₁ Γ (J ⊗ J' ∷ Δ ++ Λ₂) A =
      ⊗c (Λ₁ ++ asCxt S₁ Γ₁ ++ Γ) (Δ ++ Λ₂) _ _ (ccut-letI-s Λ₁ Λ₂ f g h)
      ∙ cong-letI1 Λ₁ Λ₂ h (~ scut-⊗c Γ Δ f g) 



  

    ccut-letI : {S₁ S₂ T : Stp} → {Γ Δ : Cxt} → (Δ₀ Λ₁ Λ₂ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
              (f : S₁ ∣ Γ ⊢ A) (g : S₂ ∣ Δ ⊢ I) (h : T ∣ Λ₁ ++ Λ₂ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
              ccut (Λ₁ ++ asCxt S₂ Δ₀) f (letI Λ₁ Λ₂ (subst-cxt r g) h) refl ≗ letI Λ₁ Λ₂ (ccut Δ₀ f g r) h
    ccut-letI Δ₀ Λ₁ Λ₂ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-letI Δ₀ Λ₁ Λ₂ f (uf g) h r with cases∷ Δ₀ r
    ccut-letI {nothing} .[] Λ₁ Λ₂ f (uf g) h refl | inj₁ (refl , refl , refl) = ccut-letI-s Λ₁ Λ₂ f g h 
    ccut-letI {just x} .[] Λ₁ Λ₂ f (uf g) h refl | inj₁ (refl , refl , refl) = ccut-letI-s Λ₁ Λ₂ f g h  
    ccut-letI .(_ ∷ Γ₀) Λ₁ Λ₂ f (uf g) h refl | inj₂ (Γ₀ , refl , refl) = ccut-letI Γ₀ Λ₁ Λ₂ f g h refl
    ccut-letI Δ₀ Λ₁ Λ₂ f Ir h r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-letI {S₁}{Γ = Γ} Δ₀ Λ₁ Λ₂ {Δ'} {A} f (Il g) h refl
      rewrite cases++-inj₂ (I ∷ Δ₀) Λ₁ (Δ' ++ Λ₂) A =
      Ic Λ₁ (Δ₀ ++ asCxt S₁ Γ ++ Δ' ++ Λ₂) (ccut-letI Δ₀ Λ₁ Λ₂ f g h refl)
    ccut-letI {S₁} {Γ = Γ} Δ₀ Λ₁ Λ₂ {Δ'} {A} f (⊗l {A = A₁} {B} g) h refl
      rewrite cases++-inj₂ (A₁ ⊗ B ∷ Δ₀) Λ₁ (Δ' ++ Λ₂) A = 
      ⊗c Λ₁ (Δ₀ ++ asCxt S₁ Γ ++ Δ' ++ Λ₂) _ _ (ccut-letI (_ ∷ Δ₀) Λ₁ Λ₂ f g h refl)
      ∙ (≡-to-≗ (cong₂ (λ x y → ⊗c Λ₁ (Δ₀ ++ asCxt S₁ Γ ++ Δ' ++ Λ₂) x y (letI Λ₁ Λ₂ (ccut (_ ∷ Δ₀) f g refl) h)) (uniq-cl _ _) (uniq-cl _ _)))
    ccut-letI Δ₀ Λ₁ Λ₂ {Δ'} f (Ic Γ Δ g) h r with  cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    ccut-letI {S₁}{S₂}{Γ = Γ} Δ₀ Λ₁ Λ₂ {.(Γ₀ ++ I ∷ Δ)} {A} f (Ic .(Δ₀ ++ A ∷ Γ₀) Δ g) h refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ (Λ₁ ++ asCxt S₂ Δ₀) Γ₀  (I ∷ Δ ++ Λ₂) A =
      Ic (Λ₁ ++ asCxt S₂ Δ₀ ++ asCxt S₁ Γ ++ Γ₀) (Δ ++ Λ₂) (ccut-letI Δ₀ Λ₁ Λ₂ f g h refl)
    ccut-letI {S₂ = S₂} .Γ Λ₁ Λ₂ {.Δ} f (Ic Γ Δ g) h refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] (Λ₁ ++ asCxt S₂ Γ) (Δ ++ Λ₂) I = ≡-to-≗ (letI-letI Γ Δ Λ₁ Λ₂ f g h)
    ccut-letI {S₁} {S₂} {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) Λ₁ Λ₂ {Δ'} {A} f (Ic Γ .(Γ₀ ++ A ∷ Δ') g) h refl | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀) (Λ₁ ++ asCxt S₂ Γ) (Δ' ++ Λ₂) A =
      Ic (Λ₁ ++ asCxt S₂ Γ) (Γ₀ ++ asCxt S₁ Γ₁ ++ Δ' ++ Λ₂) (ccut-letI (Γ ++ Γ₀) Λ₁ Λ₂ f g h refl)
    ccut-letI Δ₀ Λ₁ Λ₂ {Δ'} f (⊗c Γ Δ _ _ g) h r with  cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    ccut-letI {S₁}{S₂}{Γ = Γ} Δ₀ Λ₁ Λ₂ {.(Γ₀ ++ _ ∷ Δ)} {A} f (⊗c .(Δ₀ ++ A ∷ Γ₀) Δ {J = J}{J'} _ _ g) h refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ (Λ₁ ++ asCxt S₂ Δ₀) Γ₀  (J ⊗ J' ∷ Δ ++ Λ₂) A =
      ⊗c (Λ₁ ++ asCxt S₂ Δ₀ ++ asCxt S₁ Γ ++ Γ₀) (Δ ++ Λ₂) _ _ (ccut-letI Δ₀ Λ₁ Λ₂ f g h refl)
    ccut-letI {S₂ = S₂} .Γ Λ₁ Λ₂ {.Δ} f (⊗c Γ Δ {J = J}{J' } _ _ g) h refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] (Λ₁ ++ asCxt S₂ Γ) (Δ ++ Λ₂) (J ⊗ J') = let⊗-letI Γ Δ Λ₁ Λ₂ f g h
    ccut-letI {S₁} {S₂} {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) Λ₁ Λ₂ {Δ'} {A} f (⊗c Γ .(Γ₀ ++ A ∷ Δ') {J = J}{J'} _ _ g) h refl | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Λ₁ ++ asCxt S₂ Γ) (Δ' ++ Λ₂) A =
      ⊗c (Λ₁ ++ asCxt S₂ Γ) (Γ₀ ++ asCxt S₁ Γ₁ ++ Δ' ++ Λ₂) _ _ (ccut-letI (Γ ++ _ ∷ _ ∷ Γ₀) Λ₁ Λ₂ f g h refl)








-- ====================================================================


  mutual
    scut-ass-scut : {S : Stp} → {Γ Δ Δ' : Cxt} → {A B C : Fma}
      → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
      → scut f (scut g h) ≗ scut (scut f g) h    
    scut-ass-scut ax g h = refl
    scut-ass-scut (uf f) g h = uf (scut-ass-scut f g h)
    scut-ass-scut Ir g h = ≡-to-≗ (
      begin
      scut Ir (scut g h)
      ≡⟨ sym (Il-1-scutIr (scut g h)) ⟩
      Il-1 (scut g h)
      ≡⟨ scutIl-1 g h ⟩
      scut (Il-1 g) h
      ≡⟨ cong (λ x → scut x h) (Il-1-scutIr g) ⟩
      scut (scut Ir g) h
      ∎)
    scut-ass-scut (⊗r f f') ax h = refl
    scut-ass-scut (⊗r f f') (⊗r g g') ax = refl
    scut-ass-scut (⊗r {Γ = Γ} {Δ} f f') (⊗r {Γ = Γ₁} {Δ₁} g g') (⊗r {Γ = Γ₂} {Δ₂} h h') =
      ⊗r {Γ = Γ ++ Δ ++ Γ₁ ++ Δ₁ ++ Γ₂}{Δ₂} (scut-ass-scut (⊗r f f') (⊗r g g') h) refl
    scut-ass-scut (⊗r {Γ = Γ'}{Δ'} f f') (⊗r {Γ = Γ} g g') (⊗l h) =
      scut-ass-scut (⊗r f f') g (ccut [] g' h refl)
    scut-ass-scut (⊗r {Γ = Γ'} {Δ'} f f') (⊗r {Γ = Γ''} {Δ₁} g g') (Ic Γ Δ h) =
      Ic (Γ' ++ Δ' ++ Γ'' ++ Δ₁ ++ Γ) Δ (scut-ass-scut (⊗r f f') (⊗r g g') h)
    scut-ass-scut (⊗r {Γ = Γ'} {Δ'} f f') (⊗r {Γ = Γ''} {Δ₁} g g') (⊗c Γ Δ cJ cJ' h) =
      ⊗c (Γ' ++ Δ' ++ Γ'' ++ Δ₁ ++ Γ) Δ cJ cJ' (scut-ass-scut (⊗r f f') (⊗r g g') h)
    scut-ass-scut {Δ' = Δ'} (⊗r {Γ = Γ₁} {Δ₁} f f') (Ic Γ Δ g) h =
      Ic (Γ₁ ++ Δ₁ ++ Γ) (Δ ++ Δ') (scut-ass-scut (⊗r f f') g h)
    scut-ass-scut {Δ' = Δ'} (⊗r {Γ = Γ₁} {Δ₁} f f') (⊗c Γ Δ cJ cJ' g) h =
      ⊗c (Γ₁ ++ Δ₁ ++ Γ) (Δ ++ Δ') cJ cJ' (scut-ass-scut (⊗r f f') g h)
    scut-ass-scut (⊗r {Γ = Γ} f f') (⊗l g) h =
      cong-scut2 f (ccut-ass-scut [] f' g h refl)
      ∙ scut-ass-scut f (ccut [] f' g refl) h
    scut-ass-scut (Il f) g h = Il (scut-ass-scut f g h)
    scut-ass-scut (⊗l f) g h = ⊗l (scut-ass-scut f g h)
    scut-ass-scut {Δ = Δ₁} {Δ'} (Ic Γ Δ f) g h =
      Ic Γ (Δ ++ Δ₁ ++ Δ') (scut-ass-scut f g h)
    scut-ass-scut {Δ = Δ₁} {Δ'} (⊗c Γ Δ cJ cJ' f) g h =
      ⊗c Γ (Δ ++ Δ₁ ++ Δ') cJ cJ' (scut-ass-scut f g h)
  
  
    ccut-ass-scut : {S T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A B C : Fma}
      → (f : S ∣ Γ ⊢ A)(g : T ∣ Δ ⊢ B)(h : just B ∣ Δ'' ⊢ C)
      → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
      → ccut Δ₀ f (scut g h) (cong₂ _++_ r (refl {x = Δ''})) ≗ scut (ccut Δ₀ f g r) h
    ccut-ass-scut Δ₀ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-ass-scut Δ₀ f (uf g) h r with cases∷ Δ₀ r
    ccut-ass-scut {nothing} .[] f (uf g) h refl | inj₁ (refl , refl , refl) = scut-ass-scut f g h
    ccut-ass-scut {just x} .[] f (uf g) h refl | inj₁ (refl , refl , refl) = uf (scut-ass-scut f g h) 
    ccut-ass-scut .(_ ∷ Γ₀) f (uf g) h refl | inj₂ (Γ₀ , refl , refl) =
      uf (ccut-ass-scut Γ₀ f g h refl)
    ccut-ass-scut Δ₀ f Ir h r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-ass-scut Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g') h r with cases++ Δ₀ Γ Δ' Δ r
    ccut-ass-scut Δ₀ {.(Γ₀ ++ Δ)} {A = A} f (⊗r {Γ = .(Δ₀ ++ A ∷ Γ₀)} {Δ} g g') ax refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ Δ A = refl
    ccut-ass-scut {S} {Γ = Γ₁} Δ₀ {A = A} f (⊗r {Γ = _} {Δ} g g') (⊗r {Γ = Γ} {Δ₁} h h₁) refl | inj₁ (Γ₀ , refl , refl) with ccut-ass-scut Δ₀ f (⊗r g g') h refl
    ... | ih 
      rewrite cases++-inj₁ Δ₀ (Γ₀ ++ Δ ++ Γ) Δ₁ A | cases++-inj₁ Δ₀ Γ₀ Δ A = 
      ⊗r {Γ = Δ₀ ++ asCxt S Γ₁ ++ Γ₀ ++ Δ ++ Γ} ih refl
    ccut-ass-scut Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') (⊗l h) refl | inj₁ (Γ₀ , refl , refl) =
      ccut-ass-scut Δ₀ f g (ccut [] g' h refl) refl
    ccut-ass-scut {S} {Γ = Γ₁} Δ₀ {_} {A = A} f (⊗r {Γ = _} {Δ} g g') (Ic Γ Δ₁ h) refl | inj₁ (Γ₀ , refl , refl) with ccut-ass-scut Δ₀ f (⊗r g g') h refl
    ... | ih 
      rewrite cases++-inj₁ Δ₀ (Γ₀ ++ Δ ++ Γ) (I ∷ Δ₁) A | cases++-inj₁ Δ₀ Γ₀ Δ A =
      Ic (Δ₀ ++ asCxt S Γ₁ ++ Γ₀ ++ Δ ++ Γ) Δ₁ ih
    ccut-ass-scut {S} {Γ = Γ₁} Δ₀ {A = A} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') (⊗c Γ Δ₁ {J} {J'} cJ cJ' h) refl | inj₁ (Γ₀ , refl , refl) with ccut-ass-scut Δ₀ f (⊗r g g') h refl
    ... | ih
      rewrite cases++-inj₁ Δ₀ (Γ₀ ++ Δ ++ Γ) (J ⊗ J' ∷ Δ₁) A | cases++-inj₁ Δ₀ Γ₀ Δ A =
      ⊗c (Δ₀ ++ asCxt S Γ₁ ++ Γ₀ ++ Δ ++ Γ) Δ₁ cJ cJ' ih
    ccut-ass-scut .(Γ ++ Γ₀) {Δ'} {A = A} f (⊗r {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} g g') ax refl | inj₂ (Γ₀ , refl , refl)
      rewrite cases++-inj₂ Γ₀ Γ Δ' A = refl
    ccut-ass-scut {S} {Γ = Γ₂} ._ {Δ'} {A = A} f (⊗r {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} g g') (⊗r {Γ = Γ₁} {Δ} h h₁) refl | inj₂ (Γ₀ , refl , refl) with ccut-ass-scut (Γ ++ Γ₀) f (⊗r g g') h refl
    ... | ih 
      rewrite cases++-inj₁ (Γ ++ Γ₀) (Δ' ++ Γ₁) Δ A | cases++-inj₂ Γ₀ Γ Δ' A =
      ⊗r {Γ = Γ ++ Γ₀ ++ asCxt S Γ₂ ++ Δ' ++ Γ₁} ih refl
    ccut-ass-scut .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') (⊗l h) refl | inj₂ (Γ₀ , refl , refl) =
      ~ (≡-to-≗ (scut-par-ccut Γ₀ g f (ccut [] g' h refl) refl)) ∙ 
        (cong-scut2 g (ccut-ass-ccut Γ₀ [] f g' h refl))
    ccut-ass-scut {S} {Γ = Γ₂}.(Γ ++ Γ₀) {Δ'} {A = A} f (⊗r {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} g g') (Ic Γ₁ Δ h) refl | inj₂ (Γ₀ , refl , refl) with ccut-ass-scut (Γ ++ Γ₀) f (⊗r g g') h refl
    ... | ih
      rewrite cases++-inj₁ (Γ ++ Γ₀) (Δ' ++ Γ₁) (I ∷ Δ) A | cases++-inj₂ Γ₀ Γ Δ' A =
      Ic (Γ ++ Γ₀ ++ asCxt S Γ₂ ++ Δ' ++ Γ₁) Δ ih
    ccut-ass-scut {S} {Γ = Γ₂} .(Γ ++ Γ₀) {Δ'} {A = A} f (⊗r {Γ = Γ} g g') (⊗c Γ₁ Δ {J} {J'} cJ cJ' h) refl | inj₂ (Γ₀ , refl , refl) with ccut-ass-scut (Γ ++ Γ₀) f (⊗r g g') h refl
    ... | ih
      rewrite cases++-inj₁ (Γ ++ Γ₀) (Δ' ++ Γ₁) (J ⊗ J' ∷ Δ) A | cases++-inj₂ Γ₀ Γ Δ' A =
      ⊗c (Γ ++ Γ₀ ++ asCxt S Γ₂ ++ Δ' ++ Γ₁) Δ cJ cJ' ih
    ccut-ass-scut Δ₀ f (Il g) h refl = Il (ccut-ass-scut Δ₀ f g h refl)
    ccut-ass-scut Δ₀ f (⊗l {B = B} g) h refl = ⊗l (ccut-ass-scut (B ∷ Δ₀) f g h refl)
    ccut-ass-scut Δ₀ {Δ'} f (Ic Γ Δ g) h r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    ccut-ass-scut {S}{Γ = Γ} Δ₀ {.(Γ₀ ++ I ∷ Δ)} {Δ''} {A} f (Ic .(Δ₀ ++ A ∷ Γ₀) Δ g) h refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (I ∷ Δ ++ Δ'') A =
      Ic (Δ₀ ++ asCxt S Γ ++ Γ₀) (Δ ++ Δ'') (ccut-ass-scut Δ₀ f g h refl)
    ccut-ass-scut .Γ {.Δ} {Δ''} f (Ic Γ Δ g) h refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Γ (Δ ++ Δ'') I = ≡-to-≗ (sym (scut-letI Γ Δ f g h))
    ccut-ass-scut {S} {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} {Δ''} {A} f (Ic Γ .(Γ₀ ++ A ∷ Δ') g) h refl | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀) Γ (Δ' ++ Δ'') A =
      Ic Γ (Γ₀ ++ asCxt S Γ₁ ++ Δ' ++ Δ'') (ccut-ass-scut (Γ ++ Γ₀) f g h refl)
    ccut-ass-scut Δ₀ {Δ'} f (⊗c Γ Δ _ _ g) h r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    ccut-ass-scut {S}{Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} {Δ''} {A} f (⊗c .(Δ₀ ++ A ∷ Γ₀) Δ {J = J}{J'} _ _ g) h refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Δ ++ Δ'') A =
      ⊗c (Δ₀ ++ asCxt S Γ ++ Γ₀) (Δ ++ Δ'') _ _ (ccut-ass-scut Δ₀ f g h refl)
    ccut-ass-scut .Γ {.Δ} {Δ''} f (⊗c Γ Δ {J = J}{J'} _ _ g) h refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Γ (Δ ++ Δ'') (J ⊗ J') = ~ (scut-let⊗ Γ Δ f g h)
    ccut-ass-scut {S} {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} {Δ''} {A} f (⊗c Γ .(Γ₀ ++ A ∷ Δ') {J = J}{J'} _ _ g) h refl | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (Δ' ++ Δ'') A =
      ⊗c Γ (Γ₀ ++ asCxt S Γ₁ ++ Δ' ++ Δ'') _ _ (ccut-ass-scut (Γ ++ _ ∷ _ ∷ Γ₀) f g h refl)
  
  
    scut-let⊗ : {S T : Stp} → {Γ : Cxt} (Γ₁ Γ₂ : Cxt) {Δ : Cxt} → {A C J J' : Fma} {cJ : isCl J} {cJ' : isCl J'} → 
                (f : S ∣ Γ ⊢ J ⊗ J')  (g : T ∣ Γ₁ ++ J ∷ J' ∷ Γ₂ ⊢ A) (h : just A ∣ Δ ⊢ C) →
                scut (let⊗ Γ₁ Γ₂ cJ cJ' f g) h ≗ let⊗ Γ₁ (Γ₂ ++ Δ) cJ cJ' f (scut g h)
    scut-let⊗ Γ₁ Γ₂ ax g h = refl
    scut-let⊗ Γ₁ Γ₂ (uf f) g h = scut-let⊗ Γ₁ Γ₂ f g h
    scut-let⊗ Γ₁ Γ₂ (⊗r f f') g h =
      ~ (_∙_ (cong-ccut2 Γ₁ {f = f} refl (ccut-ass-scut (Γ₁ ++ _ ∷ []) f' g h refl))
        (ccut-ass-scut Γ₁ f (ccut (Γ₁ ++ _ ∷ []) f' g refl) h refl))
    scut-let⊗ {Γ = Γ} Γ₁ Γ₂ {Δ} (Il f) g h = Ic Γ₁ (Γ ++ Γ₂ ++ Δ) (scut-let⊗ Γ₁ Γ₂ f g h)
    scut-let⊗ {Γ = Γ} Γ₁ Γ₂ {Δ} (⊗l f) g h = ⊗c Γ₁ (Γ ++ Γ₂ ++ Δ) _ _ (scut-let⊗ Γ₁ Γ₂ f g h)
    scut-let⊗ {S} Γ₁ Γ₂ {Δ₁} (Ic Γ Δ f) g h = Ic (Γ₁ ++ asCxt S Γ) (Δ ++ Γ₂ ++ Δ₁) (scut-let⊗ Γ₁ Γ₂ f g h)
    scut-let⊗ {S} Γ₁ Γ₂ {Δ₁} (⊗c Γ Δ cJ cJ' f) g h = ⊗c (Γ₁ ++ asCxt S Γ) (Δ ++ Γ₂ ++ Δ₁) cJ cJ' (scut-let⊗ Γ₁ Γ₂ f g h)
  
    letI-let⊗ : {S₁ S₂ T : Stp} → {Γ : Cxt} → (Δ₁ Δ₂ Λ₁ Λ₂ : Cxt) → {C  J J' : Fma} {cJ : isCl J}{cJ' : isCl J'} → 
               (f : S₁ ∣ Γ ⊢ I) (g : S₂ ∣ Δ₁ ++ Δ₂ ⊢ J ⊗ J') (h : T ∣ Λ₁ ++ J ∷ J' ∷ Λ₂ ⊢ C) → 
              letI (Λ₁ ++ asCxt S₂ Δ₁) (Δ₂ ++ Λ₂) f (let⊗ Λ₁ Λ₂ cJ cJ' g h)  ≡ let⊗ Λ₁ Λ₂ cJ cJ' (letI Δ₁ Δ₂ f g) h
    letI-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ ax g h = refl
    letI-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ (uf f) g h = letI-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h
    letI-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ Ir g h = refl
    letI-let⊗ {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (Il f) g h =
      cong (Ic (Λ₁ ++ asCxt S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂)) (letI-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
    letI-let⊗ {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (⊗l f) g h =
      cong (⊗c (Λ₁ ++ asCxt S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂) _ _) (letI-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
    letI-let⊗ {S₁} {S₂} Δ₁ Δ₂ Λ₁ Λ₂ (Ic Γ Δ f) g h =
      cong (Ic (Λ₁ ++ asCxt S₂ Δ₁ ++ asCxt S₁ Γ) (Δ ++ Δ₂ ++ Λ₂)) (letI-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
    letI-let⊗ {S₁} {S₂} Δ₁ Δ₂ Λ₁ Λ₂ (⊗c Γ Δ cJ cJ' f) g h = 
      cong (⊗c (Λ₁ ++ asCxt S₂ Δ₁ ++ asCxt S₁ Γ) (Δ ++ Δ₂ ++ Λ₂) _ _) (letI-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
  
    let⊗-let⊗-s : {S T : Stp} → {Γ Δ : Cxt} → (Λ₁ Λ₂ : Cxt) → {C J J' K K' : Fma} →
                {cJ : isCl J} {cJ' : isCl J'} → {cK : isCl K} {cK' : isCl K'} → 
                (f : S ∣ Γ ⊢ J ⊗ J') (g : just J ∣ J' ∷ Δ ⊢ K ⊗ K') (h : T ∣ Λ₁ ++ K ∷ K' ∷ Λ₂ ⊢ C) → 
                let⊗ Λ₁ (Δ ++ Λ₂) cJ cJ' f (let⊗ Λ₁ Λ₂ cK cK' g h) ≗ let⊗ Λ₁ Λ₂ cK cK' (let⊗ [] Δ cJ cJ' f (uf g)) h
    let⊗-let⊗-s Λ₁ Λ₂ ax g h = refl
    let⊗-let⊗-s Λ₁ Λ₂ (uf f) g h = let⊗-let⊗-s Λ₁ Λ₂ f g h
    let⊗-let⊗-s {nothing} {Δ} Λ₁ Λ₂ (⊗r {Γ = Γ} f f₁) g h =
      ≡-to-≗ (ccut-par-ccut Λ₁ f f₁ (let⊗ Λ₁ Λ₂ _ _ g h) refl)
      ∙ cong-ccut2 (Λ₁ ++ Γ) {f = f₁} refl (ccut-let⊗-s Λ₁ Λ₂ f g h)
      ∙ ccut-let⊗ Γ Λ₁ Λ₂ f₁ (scut f g) h refl
      ∙ ≡-to-≗ (cong (λ x → let⊗ Λ₁ Λ₂ _ _ x h) (sym (scut-par-ccut [] f f₁ g refl)))
    let⊗-let⊗-s {just A} {Δ} Λ₁ Λ₂ (⊗r {Γ = Γ} f f₁) g h =
      ≡-to-≗ (ccut-par-ccut Λ₁ f f₁ (let⊗ Λ₁ Λ₂ _ _ g h) refl)
      ∙ cong-ccut2 (Λ₁ ++ A ∷ Γ) {f = f₁} refl (ccut-let⊗-s Λ₁ Λ₂ f g h)
      ∙ ccut-let⊗ Γ Λ₁ Λ₂ f₁ (scut f g) h refl
      ∙ ≡-to-≗ (cong (λ x → let⊗ Λ₁ Λ₂ _ _ x h) (sym (scut-par-ccut [] f f₁ g refl)))
    let⊗-let⊗-s {Γ = Γ} {Δ} Λ₁ Λ₂ (Il f) g h =
      Ic Λ₁ (Γ ++ Δ ++ Λ₂) (let⊗-let⊗-s Λ₁ Λ₂ f g h)
    let⊗-let⊗-s {Γ = Γ} {Δ} Λ₁ Λ₂ (⊗l f) g h = 
      ⊗c Λ₁ (Γ ++ Δ ++ Λ₂) _ _ (let⊗-let⊗-s Λ₁ Λ₂ f g h)
    let⊗-let⊗-s {S} {Δ = Δ₁} Λ₁ Λ₂ (Ic Γ Δ f) g h =
      Ic (Λ₁ ++ asCxt S Γ) (Δ ++ Δ₁ ++ Λ₂) (let⊗-let⊗-s Λ₁ Λ₂ f g h)
    let⊗-let⊗-s {S} {Δ = Δ₁} Λ₁ Λ₂ (⊗c Γ Δ cJ cJ' f) g h = 
      ⊗c (Λ₁ ++ asCxt S Γ) (Δ ++ Δ₁ ++ Λ₂) _ _ (let⊗-let⊗-s Λ₁ Λ₂ f g h)
  
    let⊗-let⊗ : {S₁ S₂ T : Stp} → {Γ : Cxt} → (Δ₁ Δ₂ Λ₁ Λ₂ : Cxt) → {C J J' K K' : Fma} →
              {cJ : isCl J} {cJ' : isCl J'} → {cK : isCl K} {cK' : isCl K'} → 
              (f : S₁ ∣ Γ ⊢ J ⊗ J') (g : S₂ ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ K ⊗ K') (h : T ∣ Λ₁ ++ K ∷ K' ∷ Λ₂ ⊢ C) → 
              let⊗ (Λ₁ ++ asCxt S₂ Δ₁) (Δ₂ ++ Λ₂) cJ cJ' f (let⊗ Λ₁ Λ₂ cK cK' g h) ≗ let⊗ Λ₁ Λ₂ cK cK' (let⊗ Δ₁ Δ₂ cJ cJ' f g) h
    let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ ax g h = refl
    let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ (uf f) g h = let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h
    let⊗-let⊗ {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (⊗r f f') g h =
      cong-ccut2 (Λ₁ ++ asCxt S₂ Δ₁) {f = f} refl (ccut-let⊗ (Δ₁ ++ _ ∷ [])  Λ₁ Λ₂ f' g h refl)
      ∙ ccut-let⊗ Δ₁ Λ₁ Λ₂ f (ccut (Δ₁ ++ _ ∷ []) f' g refl) h refl
    let⊗-let⊗ {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (Il f) g h =
      Ic (Λ₁ ++ asCxt S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂) (let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
    let⊗-let⊗ {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (⊗l f) g h =
      ⊗c (Λ₁ ++ asCxt S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂) _ _ (let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
    let⊗-let⊗ {S₁} {S₂} Δ₁ Δ₂ Λ₁ Λ₂ (Ic Γ Δ f) g h =
      Ic (Λ₁ ++ asCxt S₂ Δ₁ ++ asCxt S₁ Γ) (Δ ++ Δ₂ ++ Λ₂) (let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
    let⊗-let⊗ {S₁} {S₂} Δ₁ Δ₂ Λ₁ Λ₂ (⊗c Γ Δ cJ cJ' f) g h = 
      ⊗c (Λ₁ ++ asCxt S₂ Δ₁ ++ asCxt S₁ Γ) (Δ ++ Δ₂ ++ Λ₂) _ _ (let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
  
    ccut-let⊗-s : {S₁ T : Stp} → {Γ Δ : Cxt} → (Λ₁ Λ₂ : Cxt) → {A C  J J' : Fma} {cJ : isCl J}{cJ' : isCl J'} → 
                (f : S₁ ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ J ⊗ J') (h : T ∣ Λ₁ ++ J ∷ J' ∷ Λ₂ ⊢ C) → 
                ccut Λ₁ f (let⊗ Λ₁ Λ₂ cJ cJ' g h) refl ≗ let⊗ Λ₁ Λ₂ cJ cJ' (scut f g) h
    ccut-let⊗-s Λ₁ Λ₂ {J = J}{J'} f ax h
      rewrite cases++-inj₂ [] Λ₁ Λ₂ (J ⊗ J') = ≡-to-≗ (cong (λ x → let⊗ Λ₁ Λ₂ _ _ x h) (sym (scut-unit f)))
    ccut-let⊗-s Λ₁ Λ₂ {J = J}{J'} f (⊗r g g') h =
      ccut-ass-ccut-s Λ₁ f g (ccut (Λ₁ ++ _ ∷ []) g' h refl) refl
      ∙ (~ cong-let⊗1 Λ₁ Λ₂ h (scut⊗r f g g'))
    ccut-let⊗-s {nothing}{Δ = Δ} Λ₁ Λ₂ f (Il g) h
      rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂) I =
      ≡-to-≗ (letI-let⊗ [] Δ Λ₁ Λ₂ f g h)  ∙ cong-let⊗1 Λ₁ Λ₂ h (letI-[] Δ f g)
    ccut-let⊗-s {just _}{Δ = Δ} Λ₁ Λ₂ f (Il g) h
      rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂) I =
      ≡-to-≗ (letI-let⊗ [] Δ Λ₁ Λ₂ f g h)   ∙ cong-let⊗1 Λ₁ Λ₂ h (letI-[]-j Δ f g)
    ccut-let⊗-s {nothing} {Δ = Δ} Λ₁ Λ₂ f (⊗l {A = A} {B} g) h
      rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂)  (A ⊗ B) =
      let⊗-let⊗-s Λ₁ Λ₂ f g h ∙ cong-let⊗1 Λ₁ Λ₂ h (let⊗-[] Δ f g)  
    ccut-let⊗-s {just _} {Δ = Δ} Λ₁ Λ₂ f (⊗l {A = A} {B} g) h
      rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂)  (A ⊗ B) =
      let⊗-let⊗-s Λ₁ Λ₂ f g h  ∙ cong-let⊗1 Λ₁ Λ₂ h (let⊗-[]-j Δ f g) 
    ccut-let⊗-s {S₁}{Γ = Γ₁} Λ₁ Λ₂ {A} f (Ic Γ Δ g) h
      rewrite cases++-inj₁ Λ₁ Γ (Δ ++ Λ₂) A | cases++-inj₁ Λ₁ Γ (I ∷ Δ ++ Λ₂) A =
      Ic (Λ₁ ++ asCxt S₁ Γ₁ ++ Γ) (Δ ++ Λ₂) (ccut-let⊗-s Λ₁ Λ₂ f g h)
      ∙ cong-let⊗1 Λ₁ Λ₂ h (~ scut-Ic Γ Δ f g) 
    ccut-let⊗-s {S₁}{Γ = Γ₁} Λ₁ Λ₂ {A} f (⊗c Γ Δ {J = J}{J'} _ _ g) h
      rewrite cases++-inj₁ Λ₁ Γ (Δ ++ Λ₂) A | cases++-inj₁ Λ₁ Γ (J ⊗ J' ∷ Δ ++ Λ₂) A =
      ⊗c (Λ₁ ++ asCxt S₁ Γ₁ ++ Γ) (Δ ++ Λ₂) _ _ (ccut-let⊗-s Λ₁ Λ₂ f g h)
      ∙ cong-let⊗1 Λ₁ Λ₂ h (~ scut-⊗c Γ Δ f g) 
  
    ccut-let⊗ : {S₁ S₂ T : Stp} → {Γ Δ : Cxt} → (Δ₀ Λ₁ Λ₂ : Cxt) → {Δ' : Cxt} → {A C J J' : Fma} {cJ : isCl J}{cJ' : isCl J'} → 
               (f : S₁ ∣ Γ ⊢ A) (g : S₂ ∣ Δ ⊢ J ⊗ J') (h : T ∣ Λ₁ ++ J ∷ J' ∷ Λ₂ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
              ccut (Λ₁ ++ asCxt S₂ Δ₀) f (let⊗ Λ₁ Λ₂ cJ cJ' (subst-cxt r g) h) refl ≗ let⊗ Λ₁ Λ₂ cJ cJ' (ccut Δ₀ f g r) h
    ccut-let⊗ Δ₀ Λ₁ Λ₂ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-let⊗ Δ₀ Λ₁ Λ₂ f (uf g) h r with cases∷ Δ₀ r
    ccut-let⊗ {nothing} .[] Λ₁ Λ₂ f (uf g) h refl | inj₁ (refl , refl , refl) = ccut-let⊗-s Λ₁ Λ₂ f g h 
    ccut-let⊗ {just x} .[] Λ₁ Λ₂ f (uf g) h refl | inj₁ (refl , refl , refl) = ccut-let⊗-s Λ₁ Λ₂ f g h  
    ccut-let⊗ .(_ ∷ Γ₀) Λ₁ Λ₂ f (uf g) h refl | inj₂ (Γ₀ , refl , refl) = ccut-let⊗ Γ₀ Λ₁ Λ₂ f g h refl
    ccut-let⊗ Δ₀ Λ₁ Λ₂ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') h r with cases++ Δ₀ Γ Δ' Δ r
    ccut-let⊗ Δ₀ Λ₁ Λ₂ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') h refl | inj₁ (Γ₀ , refl , refl) =
      ccut-ass-ccut Δ₀ Λ₁ f g (ccut (Λ₁ ++ _ ∷ []) g' h refl) refl
    ccut-let⊗ .(Γ ++ Γ₀) Λ₁ Λ₂ {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') h refl | inj₂ (Γ₀ , refl , refl) =
      ≡-to-≗ (sym (ccut-par-ccut Λ₁ g f (ccut (Λ₁ ++ _ ∷ []) g' h refl) refl))
      ∙ cong-ccut2 Λ₁ {f = g} refl (ccut-ass-ccut Γ₀ (Λ₁ ++ _ ∷ []) f g' h refl)
    ccut-let⊗ {S₁}{Γ = Γ} Δ₀ Λ₁ Λ₂ {Δ'} {A} f (Il g) h refl
      rewrite cases++-inj₂ (I ∷ Δ₀) Λ₁ (Δ' ++ Λ₂) A =
      Ic Λ₁ (Δ₀ ++ asCxt S₁ Γ ++ Δ' ++ Λ₂) (ccut-let⊗ Δ₀ Λ₁ Λ₂ f g h refl)
    ccut-let⊗ {S₁} {Γ = Γ} Δ₀ Λ₁ Λ₂ {Δ'} {A} f (⊗l {A = A₁} {B} g) h refl
      rewrite cases++-inj₂ (A₁ ⊗ B ∷ Δ₀) Λ₁ (Δ' ++ Λ₂) A = 
      ⊗c Λ₁ (Δ₀ ++ asCxt S₁ Γ ++ Δ' ++ Λ₂) _ _ (ccut-let⊗ (_ ∷ Δ₀) Λ₁ Λ₂ f g h refl)
      ∙ (≡-to-≗ (cong₂ (λ x y → ⊗c Λ₁ (Δ₀ ++ asCxt S₁ Γ ++ Δ' ++ Λ₂) x y (let⊗ Λ₁ Λ₂ _ _ (ccut (_ ∷ Δ₀) f g refl) h)) (uniq-cl _ _) (uniq-cl _ _)))
    ccut-let⊗ Δ₀ Λ₁ Λ₂ {Δ'} f (Ic Γ Δ g) h r with  cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    ccut-let⊗ {S₁}{S₂}{Γ = Γ} Δ₀ Λ₁ Λ₂ {.(Γ₀ ++ I ∷ Δ)} {A} f (Ic .(Δ₀ ++ A ∷ Γ₀) Δ g) h refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ (Λ₁ ++ asCxt S₂ Δ₀) Γ₀  (I ∷ Δ ++ Λ₂) A =
      Ic (Λ₁ ++ asCxt S₂ Δ₀ ++ asCxt S₁ Γ ++ Γ₀) (Δ ++ Λ₂) (ccut-let⊗ Δ₀ Λ₁ Λ₂ f g h refl)
    ccut-let⊗ {S₂ = S₂} .Γ Λ₁ Λ₂ {.Δ} f (Ic Γ Δ g) h refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] (Λ₁ ++ asCxt S₂ Γ) (Δ ++ Λ₂) I = ≡-to-≗ (letI-let⊗ Γ Δ Λ₁ Λ₂ f g h)
    ccut-let⊗ {S₁} {S₂} {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) Λ₁ Λ₂ {Δ'} {A} f (Ic Γ .(Γ₀ ++ A ∷ Δ') g) h refl | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀) (Λ₁ ++ asCxt S₂ Γ) (Δ' ++ Λ₂) A =
      Ic (Λ₁ ++ asCxt S₂ Γ) (Γ₀ ++ asCxt S₁ Γ₁ ++ Δ' ++ Λ₂) (ccut-let⊗ (Γ ++ Γ₀) Λ₁ Λ₂ f g h refl)
    ccut-let⊗ Δ₀ Λ₁ Λ₂ {Δ'} f (⊗c Γ Δ _ _ g) h r with  cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    ccut-let⊗ {S₁}{S₂}{Γ = Γ} Δ₀ Λ₁ Λ₂ {.(Γ₀ ++ _ ∷ Δ)} {A} f (⊗c .(Δ₀ ++ A ∷ Γ₀) Δ {J = J}{J'} _ _ g) h refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ (Λ₁ ++ asCxt S₂ Δ₀) Γ₀  (J ⊗ J' ∷ Δ ++ Λ₂) A =
      ⊗c (Λ₁ ++ asCxt S₂ Δ₀ ++ asCxt S₁ Γ ++ Γ₀) (Δ ++ Λ₂) _ _ (ccut-let⊗ Δ₀ Λ₁ Λ₂ f g h refl)
    ccut-let⊗ {S₂ = S₂} .Γ Λ₁ Λ₂ {.Δ} f (⊗c Γ Δ {J = J}{J' } _ _ g) h refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] (Λ₁ ++ asCxt S₂ Γ) (Δ ++ Λ₂) (J ⊗ J') = let⊗-let⊗ Γ Δ Λ₁ Λ₂ f g h
    ccut-let⊗ {S₁} {S₂} {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) Λ₁ Λ₂ {Δ'} {A} f (⊗c Γ .(Γ₀ ++ A ∷ Δ') {J = J}{J'} _ _ g) h refl | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Λ₁ ++ asCxt S₂ Γ) (Δ' ++ Λ₂) A =
      ⊗c (Λ₁ ++ asCxt S₂ Γ) (Γ₀ ++ asCxt S₁ Γ₁ ++ Δ' ++ Λ₂) _ _ (ccut-let⊗ (Γ ++ _ ∷ _ ∷ Γ₀) Λ₁ Λ₂ f g h refl)
  
    ccut-ass-ccut-s : {S T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' Γ' : Cxt} → {A B C : Fma}
      → (f : S ∣ Γ ⊢ A)(g : just A ∣ Γ' ⊢ B)(h : T ∣ Δ ⊢ C)
      → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
      → ccut Δ₀ f (ccut Δ₀ g h r) refl ≗ ccut Δ₀ (scut f g) h r
    ccut-ass-ccut-s Δ₀ f g ax r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-ass-ccut-s Δ₀ f g (uf h) r with cases∷ Δ₀ r
    ccut-ass-ccut-s {nothing} .[] f g (uf h) refl | inj₁ (refl , refl , refl) = scut-ass-scut f g h
    ccut-ass-ccut-s {just x} .[] f g (uf h) refl | inj₁ (refl , refl , refl) = uf (scut-ass-scut f g h)
    ccut-ass-ccut-s .(_ ∷ Γ₀) f g (uf h) refl | inj₂ (Γ₀ , refl , refl) =
      uf (ccut-ass-ccut-s Γ₀ f g h refl)
    ccut-ass-ccut-s Δ₀ f g Ir r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-ass-ccut-s Δ₀ {Δ'} f g (⊗r {Γ = Γ}{Δ} h h₁) r with cases++ Δ₀ Γ Δ' Δ r 
    ccut-ass-ccut-s Δ₀ {.(Γ₀ ++ Δ)} {Γ'} {A} f g (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} h h₁) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Γ' ++ Γ₀) Δ A = ⊗r (ccut-ass-ccut-s Δ₀ f g h refl) refl
    ccut-ass-ccut-s .(Γ ++ Γ₀) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} h h₁) refl | inj₂ (Γ₀ , refl , refl)
      rewrite cases++-inj₂ Γ₀ Γ (Γ' ++ Δ') A = ⊗r refl (ccut-ass-ccut-s Γ₀ f g h₁ refl)
    ccut-ass-ccut-s Δ₀ f g (Il h) refl = Il (ccut-ass-ccut-s Δ₀ f g h refl)
    ccut-ass-ccut-s Δ₀ f g (⊗l h) refl = ⊗l (ccut-ass-ccut-s (_ ∷ Δ₀) f g h refl)
    ccut-ass-ccut-s Δ₀ {Δ'} f g (Ic Γ Δ h) r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    ccut-ass-ccut-s {S}{Γ = Γ} Δ₀ {.(Γ₀ ++ I ∷ Δ)} {Γ'} {A} f g (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ h) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Γ' ++ Γ₀) (I ∷ Δ) A = Ic (Δ₀ ++ asCxt S Γ ++ Γ' ++ Γ₀) Δ (ccut-ass-ccut-s Δ₀ f g h refl)
    ccut-ass-ccut-s .Γ {.Δ} f g (Ic Γ Δ h) refl | inj₂ ([] , refl , refl) = ccut-letI-s Γ Δ f g h
    ccut-ass-ccut-s {S}{Γ = Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} {Γ'} {A} f g (Ic Γ .(Γ₀ ++ _ ∷ Δ') h) refl | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀) Γ (Γ' ++ Δ') A = Ic Γ (Γ₀ ++ asCxt S Γ₁ ++ Γ' ++ Δ') (ccut-ass-ccut-s (Γ ++ Γ₀) f g h refl)
    ccut-ass-ccut-s Δ₀ {Δ'} f g (⊗c Γ Δ _ _ h) r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    ccut-ass-ccut-s {S}{Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} {Γ'} {A} f g (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ {J = J}{J'} _ _ h) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Γ' ++ Γ₀) (J ⊗ J' ∷ Δ) A = ⊗c (Δ₀ ++ asCxt S Γ ++ Γ' ++ Γ₀) Δ _ _ (ccut-ass-ccut-s Δ₀ f g h refl)
    ccut-ass-ccut-s .Γ {.Δ} f g (⊗c Γ Δ _ _ h) refl | inj₂ ([] , refl , refl) = ccut-let⊗-s Γ Δ f g h
    ccut-ass-ccut-s {S}{Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} {Γ'} {A} f g (⊗c Γ .(Γ₀ ++ _ ∷ Δ'){J = J}{J'} _ _ h) refl | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (Γ' ++ Δ') A = ⊗c Γ (Γ₀ ++ asCxt S Γ₁ ++ Γ' ++ Δ') _ _ (ccut-ass-ccut-s (Γ ++ _ ∷ _ ∷ Γ₀) f g h refl)
  
    
    ccut-ass-ccut : {S₁ S₂ T : Stp} → {Γ Δ : Cxt} → (Γ₀ Δ₀ : Cxt) → {Δ' Γ' : Cxt} → {A B C : Fma}
      → (f : S₁ ∣ Γ ⊢ A)(g : S₂ ∣ Γ₀ ++ A ∷ Γ' ⊢ B)(h : T ∣ Δ ⊢ C)
      → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
      → ccut (Δ₀ ++ asCxt S₂ Γ₀) f (ccut Δ₀ g h r) refl ≗ ccut Δ₀ (ccut Γ₀ f g refl) h r
    ccut-ass-ccut Γ₀ Δ₀ f g ax r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-ass-ccut Γ₀ Δ₀ f g (uf h) r with cases∷ Δ₀ r
    ccut-ass-ccut {S₁} {nothing} Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = ccut-ass-scut Γ₀ f g h refl
    ccut-ass-ccut {S₁} {just x} Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = uf (ccut-ass-scut Γ₀ f g h refl) 
    ccut-ass-ccut Γ₀ .(_ ∷ Δ₀) f g (uf h) r | inj₂ (Δ₀ , refl , refl) = uf (ccut-ass-ccut Γ₀ Δ₀ f g h refl)
    ccut-ass-ccut Γ₀ Δ₀ f g Ir r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-ass-ccut Γ₀ Δ₀ {Δ'} f g (⊗r {Γ = Γ}{Δ} h h') r with cases++ Δ₀ Γ Δ' Δ r
    ccut-ass-ccut {S₁}{S₂}{Γ = Γ} Γ₀ Δ₀ {.(Λ ++ Δ)} {Γ'} {A} f g (⊗r {Γ = .(Δ₀ ++ _ ∷ Λ)} {Δ} h h') r | inj₁ (Λ , refl , refl)
      rewrite cases++-inj₁ (Δ₀ ++ asCxt S₂ Γ₀) (Γ' ++ Λ) Δ A =
      ⊗r {Γ = Δ₀ ++ asCxt S₂ Γ₀ ++ asCxt S₁ Γ ++ Γ' ++ Λ}{Δ} (ccut-ass-ccut Γ₀ Δ₀ f g h refl) refl
    ccut-ass-ccut {S₁} {S₂} Γ₀ .(Γ ++ Λ) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Λ ++ _ ∷ Δ')} h h') r | inj₂ (Λ , refl , refl)
      rewrite cases++-inj₂ (Λ ++ asCxt S₂ Γ₀) Γ (Γ' ++ Δ') A = ⊗r refl (ccut-ass-ccut Γ₀ Λ f g h' refl)
    ccut-ass-ccut Γ₀ Δ₀ f g (Il h) refl = Il (ccut-ass-ccut Γ₀ Δ₀ f g h refl)
    ccut-ass-ccut Γ₀ Δ₀ f g (⊗l {B = B} h) refl = ⊗l (ccut-ass-ccut Γ₀ (B ∷ Δ₀) f g h refl)
    ccut-ass-ccut Γ₀ Δ₀ {Δ'} f g (Ic Γ Δ h) r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    ccut-ass-ccut {S₁}{S₂}{Γ = Γ} Γ₀ Δ₀ {.(Λ ++ I ∷ Δ)} {Γ'} {A} f g (Ic .(Δ₀ ++ _ ∷ Λ) Δ h) refl | inj₁ (Λ , refl , refl)
      rewrite cases++-inj₁ (Δ₀ ++ asCxt S₂ Γ₀) (Γ' ++ Λ) (I ∷ Δ) A =
      Ic (Δ₀ ++ asCxt S₂ Γ₀ ++ asCxt S₁ Γ ++ Γ' ++ Λ) Δ (ccut-ass-ccut Γ₀ Δ₀ f g h refl)
    ccut-ass-ccut Γ₀ .Γ {.Δ} f g (Ic Γ Δ h) refl | inj₂ ([] , refl , refl) = ccut-letI Γ₀ Γ Δ f g h refl
    ccut-ass-ccut {S₁} {S₂} {Γ = Γ₁} Γ₀ .(Γ ++ I ∷ Λ) {Δ'} {Γ'} {A} f g (Ic Γ .(Λ ++ _ ∷ Δ') h) refl | inj₂ (.I ∷ Λ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Λ ++ asCxt S₂ Γ₀) Γ (Γ' ++ Δ') A =
      Ic Γ (Λ ++ asCxt S₂ Γ₀ ++ asCxt S₁ Γ₁ ++ Γ' ++ Δ') (ccut-ass-ccut Γ₀ (Γ ++ Λ) f g h refl)
    ccut-ass-ccut Γ₀ Δ₀ {Δ'} f g (⊗c Γ Δ cJ cJ' h) r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r 
    ccut-ass-ccut {S₁}{S₂}{Γ = Γ} Γ₀ Δ₀ {.(Λ ++ _ ∷ Δ)} {Γ'} {A} f g (⊗c .(Δ₀ ++ _ ∷ Λ) Δ {J = J}{J'}_ _ h) refl | inj₁ (Λ , refl , refl)
      rewrite cases++-inj₁ (Δ₀ ++ asCxt S₂ Γ₀) (Γ' ++ Λ) (J ⊗ J' ∷ Δ) A =
      ⊗c (Δ₀ ++ asCxt S₂ Γ₀ ++ asCxt S₁ Γ ++ Γ' ++ Λ) Δ _ _ (ccut-ass-ccut Γ₀ Δ₀ f g h refl)
    ccut-ass-ccut Γ₀ .Γ {.Δ} f g (⊗c Γ Δ  {J = J}{J'} _ _ h) refl | inj₂ ([] , refl , refl) = ccut-let⊗ Γ₀ Γ Δ f g h refl
    ccut-ass-ccut {S₁} {S₂} {Γ = Γ₁} Γ₀ .(Γ ++ _ ∷ Λ) {Δ'} {Γ'} {A} f g (⊗c Γ .(Λ ++ _ ∷ Δ')  {J = J}{J'} _ _ h) refl | inj₂ (_ ∷ Λ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Λ ++ asCxt S₂ Γ₀) Γ (Γ' ++ Δ') A =
      ⊗c Γ (Λ ++ asCxt S₂ Γ₀ ++ asCxt S₁ Γ₁ ++ Γ' ++ Δ') _ _ (ccut-ass-ccut Γ₀ (Γ ++ _ ∷ _ ∷ Λ) f g h refl)







