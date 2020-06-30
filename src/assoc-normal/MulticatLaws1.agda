{-# OPTIONS --rewriting #-}

module MulticatLaws1 where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk
open import Cuts

-- ====================================================================

-- Extra laws satisfied by the cut rules (e.g. associativity, parallel
-- composition, etc.), part 1.

-- ====================================================================

-- an alternative representation of ⊗l-1

abstract
  ⊗l-1-alt : {Γ : Cxt}{A B C : Fma}(f : just (A ⊗ B) ∣ Γ ⊢ C)
    → ⊗l-1 f ≡ scut (⊗r ax (uf ax)) f
  ⊗l-1-alt ax = refl
  ⊗l-1-alt (⊗r {Γ = Γ}{Δ} f f') = cong₂ (⊗r {Γ = _ ∷ Γ}{Δ}) (⊗l-1-alt f) refl
  ⊗l-1-alt (⊗l f) = sym (ccut-unit [] f refl)
  ⊗l-1-alt (⊗c Γ Δ f) = cong (⊗c (_ ∷ Γ) Δ) (⊗l-1-alt f)

  scut⊗l-1 : {Γ Δ : Cxt} → {A B C D : Fma}
    → (f : just (A ⊗ B) ∣ Γ ⊢ C)(g : just C ∣ Δ ⊢ D)
    → ⊗l-1 (scut f g) ≡ scut (⊗l-1 f) g
  scut⊗l-1 ax g = ⊗l-1-alt g
  scut⊗l-1 (⊗r f f') ax = refl
  scut⊗l-1 (⊗r {Γ = Γ} {Δ} f f') (⊗r {Γ = Γ₁} {Δ₁} g g') = 
    cong₂ (⊗r {Γ = _ ∷ Γ ++ Δ ++ Γ₁}{Δ₁}) (scut⊗l-1 (⊗r f f') g) refl
  scut⊗l-1 {B = B} (⊗r {Γ = Γ} f f') (⊗l g) = scut⊗l-1 f (ccut _ [] f' g refl)
  scut⊗l-1 (⊗r {Γ = Γ} {Δ} f f') (⊗c Γ' Δ' g) = cong (⊗c (_ ∷ Γ ++ Δ ++ Γ') Δ') (scut⊗l-1 (⊗r f f') g)
  scut⊗l-1 (⊗l f) g = refl
  scut⊗l-1 {Δ = Δ₁} (⊗c Γ Δ f) g = cong (⊗c (_ ∷ Γ) (Δ ++ Δ₁)) (scut⊗l-1 f g)

-- ====================================================================

abstract
  mutual
    ccut-bool : {b b' : Bool} {S : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' C : Fma} → 
               (f : just A' ∣ Γ ⊢ A)  →  (g : S ∣ Δ ⊢ C)  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ') →  
                ccut b Δ₀ f g eq ≡ ccut b' Δ₀ f g eq
    ccut-bool Δ₀ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
    ccut-bool Δ₀ f (uf g) eq with cases∷ Δ₀ eq
    ccut-bool .[] f (uf g) eq | inj₁ (refl , refl , refl) = refl
    ccut-bool .(_ ∷ Γ₀) f (uf g) eq | inj₂ (Γ₀ , refl , refl) =
      cong uf (ccut-bool Γ₀ f g refl)
    ccut-bool Δ₀ f Ir eq = ⊥-elim ([]disj∷ Δ₀ eq)
    ccut-bool Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
    ccut-bool {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) eq | inj₁ (Γ₀ , refl , refl) =
      cong₂ (⊗r {Γ = Δ₀ ++ _ ∷ Γ ++ Γ₀}{Δ}) (ccut-bool Δ₀ f g refl) refl
    ccut-bool .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) eq | inj₂ (Γ₀ , refl , refl) =
      cong (⊗r g) (ccut-bool Γ₀ f g₁ refl)
    ccut-bool Δ₀ f (Il g) eq = cong Il (ccut-bool Δ₀ f g eq)
    ccut-bool Δ₀ f (⊗l g) refl = cong ⊗l (ccut-bool (_ ∷ Δ₀) f g refl)
    ccut-bool Δ₀ {Δ'} f (⊗c Γ Δ g) eq with cases++ Δ₀ Γ Δ' (_ ∷ Δ) eq
    ccut-bool {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) eq | inj₁ (Γ₀ , refl , refl) =
      cong (⊗c (Δ₀ ++ _ ∷ Γ ++ Γ₀) Δ) (ccut-bool Δ₀ f g refl)
    ccut-bool .Γ {.Δ} f (⊗c Γ Δ g) refl | inj₂ ([] , refl , refl) = let⊗-bool Γ Δ f g
    ccut-bool {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
      cong (⊗c Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')) (ccut-bool (Γ ++ _ ∷ _ ∷ Γ₀) f g refl)
  
  
    let⊗-bool : {b b' : Bool} {S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {A C J J' : Fma}
        → (f : just A ∣ Γ ⊢ J ⊗ J') (g : S ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
        → let⊗ b Δ₀ Δ₁ f g ≡ let⊗ b' Δ₀ Δ₁ f g
    let⊗-bool Δ₀ Δ₁ ax g = refl
    let⊗-bool Δ₀ Δ₁ (⊗r f f₁) g = ccut-bool Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) f₁ g refl) refl
    let⊗-bool Δ₀ Δ₁ (Il f) g = refl
    let⊗-bool Δ₀ Δ₁ (⊗l f) g = cong (⊗c Δ₀ (_ ++ Δ₁)) (let⊗-bool Δ₀ Δ₁ f g)
    let⊗-bool Δ₀ Δ₁ (⊗c Γ Δ f) g = cong (⊗c (Δ₀ ++ _ ∷ Γ) (Δ ++ Δ₁)) (let⊗-bool Δ₀ Δ₁ f g)

abstract
  IcIc : {S : Stp} (Γ Λ Δ : Cxt) {Γ' : Cxt} {A B C : Fma}
    → (f : S ∣ Γ' ⊢ C) (eq : Γ' ≡ Γ ++ A ∷ Λ ++ B ∷ Δ)
    → Ic Γ (Λ ++ I ∷ B ∷ Δ) (Ic (Γ ++ A ∷ Λ) Δ f eq) refl ≡ Ic (Γ ++ I ∷ A ∷ Λ) Δ (Ic Γ (Λ ++ B ∷ Δ) f eq) refl
  IcIc Γ Λ Δ ax eq = ⊥-elim ([]disj∷ Γ eq)
  IcIc Γ Λ Δ (uf f) eq with cases∷ Γ eq
  IcIc .[] Λ Δ (uf f) refl | inj₁ (refl , refl , refl) = refl
  IcIc .(_ ∷ Γ₀) Λ Δ (uf f) refl | inj₂ (Γ₀ , refl , refl) =
    cong uf (IcIc Γ₀ Λ Δ f refl)
  IcIc Γ Λ Δ Ir eq = ⊥-elim ([]disj∷ Γ eq)
  IcIc Γ Λ Δ {A = A} {B} (⊗r {Γ = Γ₁} {Δ₁} f f₁) eq with cases++ (Γ ++ A ∷ Λ) Γ₁ Δ Δ₁ eq
  IcIc Γ Λ .(Γ₀ ++ Δ₁) {A = A} {B} (⊗r {Γ = .(Γ ++ A ∷ Λ ++ B ∷ Γ₀)} {Δ₁} f f₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ (Λ ++ I ∷ B ∷ Γ₀) Δ₁ A | cases++-inj₁ Γ (Λ ++ B ∷ Γ₀) Δ₁ A | cases++-inj₁ (Γ ++ I ∷ A ∷ Λ) Γ₀ Δ₁ B =
    cong₂ (⊗r {Γ = Γ ++ _ ∷ _ ∷ Λ ++ _ ∷ _ ∷ Γ₀} {Δ₁}) (IcIc Γ Λ Γ₀ f refl) refl
  IcIc Γ Λ Δ {A = A} {B} (⊗r {Γ = Γ₁} {.(Γ₀ ++ B ∷ Δ)} f f₁) eq | inj₂ (Γ₀ , refl , q) with cases++ Γ Γ₁ Λ Γ₀ (sym q)
  IcIc Γ .(Γ₀' ++ Γ₀) Δ {A = A} {B} (⊗r {Γ = .(Γ ++ A ∷ Γ₀')} {.(Γ₀ ++ B ∷ Δ)} f f₁) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀' (Γ₀ ++ I ∷ B ∷ Δ) A | cases++-inj₁ Γ Γ₀' (Γ₀ ++ B ∷ Δ) A | cases++-inj₂ Γ₀ (Γ ++ I ∷ A ∷ Γ₀') Δ B = refl
  IcIc .(Γ₁ ++ Γ₀') Λ Δ {A = A} {B} (⊗r {Γ = Γ₁} {.((Γ₀' ++ A ∷ Λ) ++ B ∷ Δ)} f f₁) refl | inj₂ (.(Γ₀' ++ A ∷ Λ) , refl , refl) | inj₂ (Γ₀' , refl , refl)
    rewrite cases++-inj₂ Γ₀' Γ₁ (Λ ++ I ∷ B ∷ Δ) A | cases++-inj₂ Γ₀' Γ₁ (Λ ++ B ∷ Δ) A | cases++-inj₂ (Γ₀' ++ I ∷ A ∷ Λ) Γ₁ Δ B  =
    cong (⊗r f) (IcIc Γ₀' Λ Δ f₁ refl)
  IcIc Γ Λ Δ (Il f) eq = cong Il (IcIc Γ Λ Δ f eq)
  IcIc Γ Λ Δ (⊗l f) refl = cong ⊗l (IcIc (_ ∷ Γ) Λ Δ f refl)
  IcIc Γ Λ Δ {A = A} (⊗c Γ₁ Δ₁ {J} {J'} f) eq with  cases++ (Γ ++ A ∷ Λ) Γ₁ Δ (J ⊗ J' ∷ Δ₁) eq
  IcIc Γ Λ .(Γ₀ ++ J ⊗ J' ∷ Δ₁) {A = A}{B} (⊗c .(Γ ++ A ∷ Λ ++ _ ∷ Γ₀) Δ₁ {J} {J'} f) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ (Λ ++ I ∷ B ∷ Γ₀) (J ⊗ J' ∷ Δ₁) A | cases++-inj₁ Γ (Λ ++ B ∷ Γ₀) (J ⊗ J' ∷ Δ₁) A | cases++-inj₁ (Γ ++ I ∷ A ∷ Λ) Γ₀ (J ⊗ J' ∷ Δ₁) B =
    cong (⊗c (Γ ++ I ∷ A ∷ Λ ++ I ∷ B ∷ Γ₀) Δ₁) (IcIc Γ Λ (Γ₀ ++ J ∷ J' ∷ Δ₁) f refl)
  IcIc Γ Λ .Δ₁ {A = A} (⊗c .(Γ ++ A ∷ Λ) Δ₁ {J} {J'} f) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₁ Γ (Λ ++ I ∷ []) (J ⊗ J' ∷ Δ₁) A | cases++-inj₁ Γ Λ (J ⊗ J' ∷ Δ₁) A | cases++-inj₂ [] (Γ ++ I ∷ A ∷ Λ) Δ₁ (J ⊗ J')  =
    cong (⊗c (Γ ++ I ∷ A ∷ Λ ++ I ∷ []) Δ₁) (IcIc Γ Λ  (J' ∷ Δ₁) f refl)
  IcIc Γ Λ Δ {A = A} (⊗c Γ₁ .(Γ₀ ++ _ ∷ Δ) {J} {J'} f) eq | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , q) with cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Γ₀) (sym q)
  IcIc Γ .(Γ₀' ++ J ⊗ J' ∷ Γ₀) Δ {A = A} {B} (⊗c .(Γ ++ A ∷ Γ₀') .(Γ₀ ++ B ∷ Δ) {J} {J'} f) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀' (J ⊗ J' ∷ Γ₀ ++ I ∷ B ∷ Δ) A | cases++-inj₁ Γ Γ₀' (J ⊗ J' ∷ Γ₀ ++ B ∷ Δ) A | cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Γ ++ I ∷ A ∷ Γ₀') Δ B =
    cong (⊗c (Γ ++ I ∷ A ∷ Γ₀') (Γ₀ ++ I ∷ B ∷ Δ)) (IcIc Γ (Γ₀' ++ J ∷ J' ∷ Γ₀) Δ f refl)
  IcIc .Γ₁ .Γ₀ Δ {A = .(J ⊗ J')} {B} (⊗c Γ₁ .(Γ₀ ++ B ∷ Δ) {J} {J'} f) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ₁ (Γ₀ ++ I ∷ B ∷ Δ) (J ⊗ J') | cases++-inj₂ [] Γ₁ (Γ₀ ++ B ∷ Δ) (J ⊗ J') | cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Γ₁ ++ I ∷ []) Δ B =
    cong (⊗c (Γ₁ ++ I ∷ []) (Γ₀ ++ I ∷ B ∷ Δ)) (IcIc Γ₁ (J' ∷ Γ₀) Δ f refl)
  IcIc .(Γ₁ ++ J ⊗ J' ∷ Γ₀') Λ Δ {A = A} {B} (⊗c Γ₁ .((Γ₀' ++ A ∷ Λ) ++ B ∷ Δ) {J} {J'} f) refl | inj₂ (.(J ⊗ J') ∷ .(Γ₀' ++ A ∷ Λ) , refl , refl) | inj₂ (.(J ⊗ J') ∷ Γ₀' , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ₁ (Λ ++ I ∷ B ∷ Δ) A | cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ₁ (Λ ++ B ∷ Δ) A | cases++-inj₂ ( J ⊗ J' ∷ Γ₀' ++ I ∷ A ∷ Λ) Γ₁ Δ B  =
    cong (⊗c Γ₁ (Γ₀' ++ I ∷ A ∷ Λ ++ I ∷ B ∷ Δ)) (IcIc (Γ₁ ++ J ∷ J' ∷ Γ₀')  Λ Δ f refl)

abstract
  IcIc2 : {S : Stp} (Γ Λ : Cxt) {Γ' : Cxt} {A C : Fma}
    → (f : S ∣ Γ' ⊢ C) (eq : Γ' ≡ Γ ++ A ∷ Λ)
    → Ic Γ (A ∷ Λ) (Ic Γ Λ f eq) refl ≡ Ic (Γ ++ I ∷ []) Λ (Ic Γ Λ f eq) refl
  IcIc2 Γ Λ ax eq = ⊥-elim ([]disj∷ Γ eq)
  IcIc2 Γ Λ (uf f) eq with cases∷ Γ eq
  IcIc2 .[] Λ (uf f) refl | inj₁ (refl , refl , refl) = refl
  IcIc2 .(_ ∷ Γ₀) Λ (uf f) refl | inj₂ (Γ₀ , refl , refl) = cong uf (IcIc2 Γ₀ Λ f refl)
  IcIc2 Γ Λ Ir eq = ⊥-elim ([]disj∷ Γ eq)
  IcIc2 Γ Λ (⊗r {Γ = Γ₁} {Δ} f f₁) eq with  cases++ Γ Γ₁ Λ Δ eq
  IcIc2 Γ .(Γ₀ ++ Δ) {A = A} (⊗r {Γ = .(Γ ++ A ∷ Γ₀)} {Δ} f f₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ (A ∷ Γ₀) Δ I | cases++-inj₁ (Γ ++ I ∷ []) Γ₀ Δ A =
    cong₂ (⊗r {Γ = Γ ++ _ ∷ _ ∷ _ ∷ Γ₀} {Δ}) (IcIc2 Γ Γ₀ f refl) refl
  IcIc2 .(Γ₁ ++ Γ₀) Λ {A = A} (⊗r {Γ = Γ₁} {.(Γ₀ ++ A ∷ Λ)} f f₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ₁ (A ∷ Λ) I | cases++-inj₂ (Γ₀ ++ I ∷ []) Γ₁ Λ A = cong (⊗r f) (IcIc2 Γ₀ Λ f₁ refl)
  IcIc2 Γ Λ (Il f) eq = cong Il (IcIc2 Γ Λ f eq)
  IcIc2 Γ Λ (⊗l f) refl = cong ⊗l (IcIc2 (_ ∷ Γ) Λ f refl)
  IcIc2 Γ Λ (⊗c Γ₁ Δ {J} {J'} f) eq with cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Δ) eq
  IcIc2 Γ .(Γ₀ ++ J ⊗ J' ∷ Δ) {A = A} (⊗c .(Γ ++ A ∷ Γ₀) Δ {J} {J'} f) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ (A ∷ Γ₀) (J ⊗ J' ∷ Δ) I | cases++-inj₁ (Γ ++ I ∷ []) Γ₀  (J ⊗ J' ∷ Δ) A =
    cong (⊗c (Γ ++ I ∷ I ∷ A ∷ Γ₀) Δ) (IcIc2 Γ (Γ₀ ++ J ∷ J' ∷ Δ) f refl)
  IcIc2 .Γ₁ .Δ (⊗c Γ₁ Δ {J} {J'} f) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₁ Γ₁ [] (J ⊗ J' ∷ Δ) I | cases++-inj₂ []  (Γ₁ ++ I ∷ []) Δ (J ⊗ J') =
    cong (⊗c (Γ₁ ++ I ∷ I ∷ []) Δ) (IcIc2 Γ₁ (J' ∷ Δ) f refl)
  IcIc2 .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ {A = A} (⊗c Γ₁ .(Γ₀ ++ A ∷ Λ) {J} {J'} f) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ₁ (A ∷ Λ) I | cases++-inj₂ (J ⊗ J' ∷ Γ₀ ++ I ∷ []) Γ₁ Λ A =
    cong (⊗c Γ₁ (Γ₀ ++ I ∷ I ∷ A ∷ Λ)) (IcIc2 (Γ₁ ++ J ∷ J' ∷ Γ₀)  Λ f refl)
  
abstract  
  ccut-Ic21 : (b : Bool) {T S : Stp} → {Δ Γ : Cxt} → (Δ₀ Δ₁ : Cxt) → {Δ' : Cxt} → {A B C : Fma} → 
            (f : T ∣ Γ ⊢ A) (g : S ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁ ++ B ∷ Δ') →  
            ccut b Δ₀ f (Ic (Δ₀ ++ A ∷ Δ₁) Δ' g eq) refl ≡ Ic (Δ₀ ++ asCxt b T Γ ++ Δ₁) Δ' (ccut b Δ₀ f g eq) refl
  ccut-Ic22 : (b : Bool) {T S : Stp} → {Δ Γ : Cxt} → (Δ₀ Δ₁ : Cxt) → {Δ' : Cxt} → {A B C : Fma} → 
             (f : T ∣ Γ ⊢ A) (g : S ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁ ++ A ∷ Δ') →  
             ccut b (Δ₀ ++ I ∷ B ∷ Δ₁) f (Ic Δ₀ (Δ₁ ++ A ∷ Δ') g eq) refl ≡ Ic Δ₀ (Δ₁ ++ asCxt b T Γ ++ Δ') (ccut b (Δ₀ ++ B ∷ Δ₁) f g eq) refl
  let⊗-Ic21 : (b : Bool) {T S : Stp} → (Γ₁ Δ₁ : Cxt) → {Δ₂ Γ : Cxt} → {A J J' C : Fma} → 
             (f : T ∣ Γ ⊢ J ⊗ J') (g : S ∣ Γ₁ ++ J ∷ J' ∷ Δ₁ ++ A ∷ Δ₂ ⊢ C) → 
             let⊗ b Γ₁ (Δ₁ ++ I ∷ A ∷ Δ₂) f (Ic (Γ₁ ++ J ∷ J' ∷ Δ₁) Δ₂ g refl) ≡
               Ic (Γ₁ ++ asCxt b T Γ ++ Δ₁) Δ₂ (let⊗ b Γ₁ (Δ₁ ++ A ∷ Δ₂) f g) refl
  let⊗-Ic22 : (b : Bool) {T S : Stp} → (Γ₁ Δ₁ : Cxt) → {Δ₂ Γ : Cxt} → {A J J' C : Fma} → 
             (f : T ∣ Γ ⊢ J ⊗ J') (g : S ∣ Δ₁ ++ A ∷ Δ₂ ++ J ∷ J' ∷ Γ₁ ⊢ C) → 
             let⊗ b (Δ₁ ++ I ∷ A ∷ Δ₂) Γ₁ f (Ic Δ₁ (Δ₂ ++ J ∷ J' ∷ Γ₁) g refl) ≡
               Ic Δ₁ (Δ₂ ++ asCxt b T Γ ++ Γ₁) (let⊗ b (Δ₁ ++ A ∷ Δ₂) Γ₁ f g) refl
  let⊗-Ic1 : (b : Bool) {T S : Stp} → (Γ Γ₁ Δ Λ : Cxt) → {Γ' : Cxt} → {A J J' C : Fma} → 
             (f : T ∣ Γ' ⊢ J ⊗ J') (g : S ∣ Γ₁ ++ J ∷ J' ∷ Δ ⊢ C) (eq : Γ' ≡ Γ ++ A ∷ Λ) →  
             let⊗ b Γ₁ Δ (Ic Γ Λ f eq) g ≡ Ic (Γ₁ ++ asCxt b T Γ) (Λ ++ Δ) (let⊗ b Γ₁ Δ f g) (cong (λ x → Γ₁ ++ asCxt b T x ++ Δ) eq)
  ccut-Ic1 : (b : Bool) {T S : Stp} → {Δ : Cxt} → (Δ₀ Γ Λ : Cxt) → {Δ' : Cxt} → {A B C : Fma} → 
             (f : T ∣ Γ ++ B ∷ Λ ⊢ A) (g : S ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ') →  
             ccut b Δ₀ (Ic Γ Λ f refl) g eq ≡ Ic (Δ₀ ++ asCxt b T Γ) (Λ ++ Δ') (ccut b Δ₀ f g eq) refl
  scut-Ic2 : {S : Stp} (Γ Λ : Cxt) {Γ' Δ : Cxt} → {A B C : Fma} → 
              (f : S ∣ Δ ⊢ B) (g : just B ∣ Γ' ⊢ C) (eq : Γ' ≡ Γ ++ A ∷ Λ) →
              scut f (Ic Γ Λ g eq) ≡ Ic (Δ ++ Γ) Λ (scut f g) (cong (Δ ++_){x = Γ'}{Γ ++ A ∷ Λ} eq)
  scut-Ic1 : {S : Stp} (Γ Λ : Cxt) {Γ' Δ : Cxt} → {A B C : Fma} → 
              (f : S ∣ Γ' ⊢ B) (g : just B ∣ Δ ⊢ C) (eq : Γ' ≡ Γ ++ A ∷ Λ) →
              scut (Ic Γ Λ f eq) g ≡ Ic Γ (Λ ++ Δ) (scut f g) (cong (λ x → x ++ Δ) {x = Γ'}{Γ ++ A ∷ Λ} eq)
  
  ccut-Ic21 b Δ₀ Δ₁ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic21 b Δ₀ Δ₁ f (uf g) eq with cases∷ Δ₀ eq
  ccut-Ic21 b {just x} .[] Δ₁ f (uf g) refl | inj₁ (refl , refl , refl) = cong uf (scut-Ic2 Δ₁ _ f g refl)
  ccut-Ic21 false {nothing} .[] Δ₁ f (uf g) refl | inj₁ (refl , refl , refl) = scut-Ic2 Δ₁ _ f g refl
  ccut-Ic21 true {nothing} .[] Δ₁ f (uf g) refl | inj₁ (refl , refl , refl) = cong uf (cong Il (scut-Ic2 Δ₁ _ f g refl))
  ccut-Ic21 b .(_ ∷ Γ₀) Δ₁ f (uf g) refl | inj₂ (Γ₀ , refl , refl) = cong uf (ccut-Ic21 b Γ₀ Δ₁ f g refl)
  ccut-Ic21 b Δ₀ Δ₁ f Ir eq = ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic21 b Δ₀ Δ₁ {Δ'} {A} {B} f (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ (Δ₀ ++ A ∷ Δ₁) Γ Δ' Δ eq
  ccut-Ic21 b {T} {Γ = Γ} Δ₀ Δ₁ {.(Γ₀ ++ Δ)} {A} {B} f (⊗r {Γ = .(Δ₀ ++ A ∷ Δ₁ ++ B ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Δ₁ ++ I ∷ B ∷ Γ₀) Δ A | cases++-inj₁ Δ₀ (Δ₁ ++ B ∷ Γ₀) Δ A | cases++-inj₁ (Δ₀ ++ asCxt b T Γ ++ Δ₁) Γ₀ Δ B =
    cong₂ (⊗r {Γ = Δ₀ ++ asCxt b T Γ ++ Δ₁ ++ _ ∷ _ ∷ Γ₀} {Δ}) (ccut-Ic21 b Δ₀ Δ₁ f g refl) refl
  ccut-Ic21 b Δ₀ Δ₁ {Δ'} {A} {B} f (⊗r {Γ = Γ} {.(Γ₀ ++ B ∷ Δ')} g g₁) eq | inj₂ (Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym q)
  ccut-Ic21 b {T₁} {Γ = Γ} Δ₀ .(Γ₀' ++ Γ₀) {Δ'} {A} {B} f (⊗r {Γ = .(Δ₀ ++ A ∷ Γ₀')} {.(Γ₀ ++ B ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ I ∷ B ∷ Δ') A | cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ B ∷ Δ') A | cases++-inj₂ Γ₀  (Δ₀ ++ asCxt b T₁ Γ ++ Γ₀') Δ' B = refl
  ccut-Ic21 b {T₁} {Γ = Γ₁} .(Γ ++ Γ₀') Δ₁ {Δ'} {A} {B} f (⊗r {Γ = Γ} {.((Γ₀' ++ A ∷ Δ₁) ++ B ∷ Δ')} g g₁) refl | inj₂ (.(Γ₀' ++ A ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , refl , refl)
    rewrite cases++-inj₂ Γ₀' Γ (Δ₁ ++ I ∷ B ∷ Δ') A | cases++-inj₂ Γ₀' Γ (Δ₁ ++ B ∷ Δ') A | cases++-inj₂ (Γ₀' ++ asCxt b T₁ Γ₁ ++ Δ₁) Γ Δ' B =
    cong (⊗r g) (ccut-Ic21 b Γ₀' Δ₁ f g₁ refl)
  ccut-Ic21 b Δ₀ Δ₁ f (Il g) eq = cong Il (ccut-Ic21 b Δ₀ Δ₁ f g eq)
  ccut-Ic21 b Δ₀ Δ₁ f (⊗l g) refl = cong ⊗l (ccut-Ic21 b (_ ∷ Δ₀) Δ₁ f g refl)
  ccut-Ic21 b Δ₀ Δ₁ {Δ'} {A} {B} f (⊗c Γ Δ {J} {J'} g) eq with cases++ (Δ₀ ++ A ∷ Δ₁) Γ Δ' (J ⊗ J' ∷ Δ) eq
  ccut-Ic21 b {T₁} {Γ = Γ} Δ₀ Δ₁ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} {A} {B} f (⊗c .(Δ₀ ++ A ∷ Δ₁ ++ B ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Δ₁ ++ I ∷ B ∷ Γ₀) (J ⊗ J' ∷ Δ) A | cases++-inj₁ Δ₀ (Δ₁ ++ B ∷ Γ₀) (J ⊗ J' ∷ Δ) A | cases++-inj₁ (Δ₀ ++ asCxt b T₁ Γ ++ Δ₁) Γ₀ (J ⊗ J' ∷ Δ) B =
    cong (⊗c (Δ₀ ++ asCxt b T₁ Γ ++ Δ₁ ++ I ∷ B ∷ Γ₀) Δ) (ccut-Ic21 b Δ₀ Δ₁ f g refl)
  ccut-Ic21 b {T₁} {Γ = Γ} Δ₀ Δ₁ {.Δ} {A} {.(J ⊗ J')} f (⊗c .(Δ₀ ++ A ∷ Δ₁) Δ {J} {J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Δ₁ ++ I ∷ []) (J ⊗ J' ∷ Δ) A | cases++-inj₁ Δ₀ Δ₁ (J ⊗ J' ∷ Δ) A | cases++-inj₂ [] (Δ₀ ++ asCxt b T₁ Γ ++ Δ₁) Δ (J ⊗ J') =
    cong (⊗c (Δ₀ ++ asCxt b T₁ Γ ++ Δ₁ ++ I ∷ []) Δ) (ccut-Ic21 b Δ₀ Δ₁ f g refl )
  ccut-Ic21 b {T₁} {Γ = Γ₁} Δ₀ Δ₁ {Δ'} {A} {B} f (⊗c Γ .(Γ₀ ++ B ∷ Δ') {J} {J'} g) eq | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ (J ⊗ J' ∷ Γ₀) (sym q)
  ccut-Ic21 b {T₁} {Γ = Γ₁} Δ₀ .(Γ₀' ++ J ⊗ J' ∷ Γ₀) {Δ'} {A} {B} f (⊗c .(Δ₀ ++ A ∷ Γ₀') .(Γ₀ ++ B ∷ Δ') {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ Δ₀ Γ₀'  (J ⊗ J' ∷ Γ₀ ++ I ∷ B ∷ Δ') A |  cases++-inj₁ Δ₀ Γ₀'  (J ⊗ J' ∷ Γ₀ ++ B ∷ Δ') A | cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Δ₀ ++ asCxt b T₁ Γ₁ ++ Γ₀') Δ' B =
    cong (⊗c (Δ₀ ++ asCxt b T₁ Γ₁ ++ Γ₀') (Γ₀ ++ I ∷ B ∷ Δ')) (ccut-Ic21 b Δ₀ (Γ₀' ++ J ∷ J' ∷ Γ₀) f g refl )
  ccut-Ic21 b {T₁} {Γ = Γ₁} .Γ .Γ₀ {Δ'} {.(J ⊗ J')} {B} f (⊗c Γ .(Γ₀ ++ B ∷ Δ') {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ (Γ₀ ++ I ∷ B ∷ Δ') (J ⊗ J') | cases++-inj₂ [] Γ (Γ₀ ++ B ∷ Δ') (J ⊗ J') = let⊗-Ic21 b Γ Γ₀ f g 
  ccut-Ic21 b {T₁} {Γ = Γ₁} .(Γ ++ J ⊗ J' ∷ Γ₀') Δ₁ {Δ'} {A} {B} f (⊗c Γ ._ {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ .(Γ₀' ++ A ∷ Δ₁) , refl , refl) | inj₂ (.(J ⊗ J') ∷ Γ₀' , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Δ₁ ++ I ∷ B ∷ Δ') A |  cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Δ₁ ++ B ∷ Δ') A | cases++-inj₂ (J ⊗ J' ∷ Γ₀' ++ asCxt b T₁ Γ₁ ++ Δ₁) Γ Δ' B =
    cong (⊗c Γ (Γ₀' ++ asCxt b T₁ Γ₁ ++ Δ₁ ++ I ∷ B ∷ Δ')) (ccut-Ic21 b (Γ ++ J ∷ J' ∷ Γ₀') Δ₁ f g refl)
  
  ccut-Ic22 b Δ₀ Δ₁ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic22 b Δ₀ Δ₁ f (uf g) eq with cases∷ Δ₀ eq
  ccut-Ic22 b .[] Δ₁ f (uf g) refl | inj₁ (refl , refl , refl) = refl
  ccut-Ic22 b .(_ ∷ Γ₀) Δ₁ f (uf g) refl | inj₂ (Γ₀ , refl , refl) = cong uf (ccut-Ic22 b Γ₀ Δ₁ f g refl)
  ccut-Ic22 b Δ₀ Δ₁ f Ir eq = ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic22 b {T₁} {Γ = Γ} Δ₀ Δ₁ {Δ'} {A} {B} f (⊗r {Γ = Γ₁} {Δ} g g₁) eq with cases++ Δ₀ Γ₁ (Δ₁ ++ A ∷ Δ') Δ eq
  ccut-Ic22 b {T₁} {Γ = Γ} Δ₀ Δ₁ {Δ'} {A} {B} f (⊗r {Γ = .(Δ₀ ++ B ∷ Γ₀)} {Δ} g g₁) eq | inj₁ (Γ₀ , refl , q) with cases++ Δ₁ Γ₀ Δ' Δ (sym q)
  ccut-Ic22 b {T₁} {Γ = Γ} Δ₀ Δ₁ {.(Γ₀' ++ Δ)} {A} {B} f (⊗r {_} {.(Δ₀ ++ B ∷ Δ₁ ++ A ∷ Γ₀')} {Δ} g g₁) refl | inj₁ (.(Δ₁ ++ A ∷ Γ₀') , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ (Δ₀ ++ I ∷ B ∷ Δ₁) Γ₀' Δ A | cases++-inj₁ (Δ₀ ++ B ∷ Δ₁) Γ₀' Δ A | cases++-inj₁ Δ₀ (Δ₁ ++ asCxt b T₁ Γ ++ Γ₀') Δ B =
    cong₂ (⊗r {Γ = Δ₀ ++ I ∷ B ∷ Δ₁ ++ asCxt b T₁ Γ ++ Γ₀'} {Δ}) (ccut-Ic22 b Δ₀ Δ₁ f g refl) refl
  ccut-Ic22 b {T₁} {Γ = Γ} Δ₀ .(Γ₀ ++ Γ₀') {Δ'} {A} {B} f (⊗r {_} {.(Δ₀ ++ B ∷ Γ₀)} {.(Γ₀' ++ A ∷ Δ')} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl)
    rewrite cases++-inj₂ Γ₀' (Δ₀ ++ I ∷ B ∷ Γ₀) Δ' A | cases++-inj₂ Γ₀' (Δ₀ ++ B ∷ Γ₀) Δ' A | cases++-inj₁ Δ₀ Γ₀ (Γ₀' ++ asCxt b T₁ Γ ++ Δ')  B = refl
  ccut-Ic22 b {T₁} {Γ = Γ} .(Γ₁ ++ Γ₀) Δ₁ {Δ'} {A} {B} f (⊗r {Γ = Γ₁} {.(Γ₀ ++ B ∷ Δ₁ ++ A ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ (Γ₀ ++ I ∷ B ∷ Δ₁) Γ₁ Δ' A | cases++-inj₂ (Γ₀ ++ B ∷ Δ₁) Γ₁ Δ' A | cases++-inj₂ Γ₀ Γ₁ (Δ₁ ++ asCxt b T₁ Γ ++ Δ') B =
    cong (⊗r g) (ccut-Ic22 b Γ₀ Δ₁ f g₁ refl) 
  ccut-Ic22 b Δ₀ Δ₁ f (Il g) eq = cong Il (ccut-Ic22 b Δ₀ Δ₁ f g eq)
  ccut-Ic22 b Δ₀ Δ₁ f (⊗l g) refl = cong ⊗l (ccut-Ic22 b (_ ∷ Δ₀) Δ₁ f g refl)
  ccut-Ic22 b {T₁} {Γ = Γ₁} Δ₀ Δ₁ {Δ'} {A} {B} f (⊗c Γ Δ {J} {J'} g) eq with cases++ Δ₀ Γ (Δ₁ ++ A ∷ Δ') (J ⊗ J' ∷ Δ) eq 
  ccut-Ic22 b {T₁} {Γ = Γ₁} Δ₀ Δ₁ {Δ'} {A} {B} f (⊗c .(Δ₀ ++ B ∷ Γ₀) Δ {J} {J'} g) eq | inj₁ (Γ₀ , refl , q) with cases++ Δ₁ Γ₀ Δ' (J ⊗ J' ∷ Δ) (sym q)
  ccut-Ic22 b {T₁} {Γ = Γ₁} Δ₀ Δ₁ {.(Γ₀' ++ J ⊗ J' ∷ Δ)} {A} {B} f (⊗c .(Δ₀ ++ B ∷ Δ₁ ++ A ∷ Γ₀') Δ {J} {J'} g) refl | inj₁ (.(Δ₁ ++ A ∷ Γ₀') , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ (Δ₀ ++ I ∷ B ∷ Δ₁) Γ₀'  (J ⊗ J' ∷ Δ) A | cases++-inj₁ (Δ₀ ++ B ∷ Δ₁) Γ₀'  (J ⊗ J' ∷ Δ) A | cases++-inj₁ Δ₀ (Δ₁ ++ asCxt b T₁ Γ₁ ++ Γ₀') (J ⊗ J' ∷ Δ) B =
    cong (⊗c (Δ₀ ++ I ∷ B ∷ Δ₁ ++ asCxt b T₁ Γ₁ ++ Γ₀') Δ) (ccut-Ic22 b Δ₀ Δ₁ f g refl)
  ccut-Ic22 b {T₁} {Γ = Γ₁} Δ₀ .Γ₀ {.Δ} {.(J ⊗ J')} {B} f (⊗c .(Δ₀ ++ B ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] (Δ₀ ++ I ∷ B ∷ Γ₀) Δ (J ⊗ J') | cases++-inj₂ [] (Δ₀ ++ B ∷ Γ₀) Δ (J ⊗ J') = let⊗-Ic22 b Δ Δ₀ f g
  ccut-Ic22 b {T₁} {Γ = Γ₁} Δ₀ .(Γ₀ ++ J ⊗ J' ∷ Γ₀') {Δ'} {A} {B} f (⊗c .(Δ₀ ++ B ∷ Γ₀) .(Γ₀' ++ A ∷ Δ') {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl) | inj₂ (.(J ⊗ J') ∷ Γ₀' , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') (Δ₀ ++ B ∷ Γ₀) Δ' A | cases++-inj₂ (J ⊗ J' ∷ Γ₀') (Δ₀ ++ I ∷ B ∷ Γ₀) Δ' A | cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Γ₀' ++ asCxt b T₁ Γ₁ ++ Δ') B =
    cong (⊗c (Δ₀ ++ I ∷ B ∷ Γ₀) (Γ₀' ++ asCxt b T₁ Γ₁ ++ Δ')) (ccut-Ic22 b Δ₀ (Γ₀ ++ J ∷ J' ∷ Γ₀') f g refl)
  ccut-Ic22 b {T₁} {Γ = Γ₁} .Γ Δ₁ {Δ'} {A} {.(J ⊗ J')} f (⊗c Γ .(Δ₁ ++ A ∷ Δ') {J} {J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Δ₁) (Γ ++ I ∷ []) Δ' A | cases++-inj₂ (J ⊗ J' ∷ Δ₁) Γ Δ' A | cases++-inj₂ [] Γ (Δ₁ ++ asCxt b T₁ Γ₁ ++ Δ') (J ⊗ J') =
    cong (⊗c (Γ ++ I ∷ []) (Δ₁ ++ asCxt b T₁ Γ₁ ++ Δ')) (ccut-Ic22 b Γ (J' ∷ Δ₁) f g refl )
  ccut-Ic22 b {T₁} {Γ = Γ₁} .(Γ ++ J ⊗ J' ∷ Γ₀) Δ₁ {Δ'} {A} {B} f (⊗c Γ .(Γ₀ ++ B ∷ Δ₁ ++ A ∷ Δ') {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀ ++ I ∷ B ∷ Δ₁) Γ Δ' A | cases++-inj₂ (J ⊗ J' ∷ Γ₀ ++ B ∷ Δ₁) Γ Δ' A | cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (Δ₁ ++ asCxt b T₁ Γ₁ ++ Δ') B =
    cong (⊗c Γ (Γ₀ ++ I ∷ B ∷ Δ₁ ++ asCxt b T₁ Γ₁ ++ Δ')) (ccut-Ic22 b (Γ ++ J ∷ J' ∷ Γ₀) Δ₁ f g refl)
  
  let⊗-Ic21 b Γ₁ Δ₁  {Δ₂} {A = A} {J} {J'} ax g
    rewrite cases++-inj₂ ( J ⊗ J' ∷ Δ₁) Γ₁ Δ₂ A = refl
  let⊗-Ic21 false Γ₁ Δ₁  (uf f) g = let⊗-Ic21 _ Γ₁ Δ₁  f g
  let⊗-Ic21 true Γ₁ Δ₁  {Δ₂} (uf {Γ = Γ} f) g =
    trans (cong (λ x → Ic Γ₁ (Γ ++ Δ₁ ++ I ∷ _ ∷ Δ₂) x refl) (let⊗-Ic21 true Γ₁ Δ₁ f g))
      (IcIc Γ₁ (Γ ++ Δ₁) Δ₂ (let⊗ true Γ₁ (Δ₁ ++ _ ∷ Δ₂) f g) refl)
  let⊗-Ic21 b Γ₁ Δ₁  (⊗r {Γ = Γ₂}{Δ₂} f f₁) g =
    trans (cong (λ x → ccut b Γ₁ f x refl) (ccut-Ic21 false (Γ₁ ++ _ ∷ []) Δ₁ f₁ g refl) )
      (ccut-Ic21 b Γ₁ (Δ₂ ++ Δ₁) f (ccut false (Γ₁ ++ _ ∷ []) f₁ g refl) refl)
  let⊗-Ic21 b Γ₁ Δ₁  (Il f) g = let⊗-Ic21 _ Γ₁ Δ₁  f g
  let⊗-Ic21 b Γ₁ Δ₁  {Δ₂} {Γ} {A} (⊗l {A = A₁} {B} f) g
    rewrite cases++-inj₂ (A₁ ⊗ B ∷ Γ ++ Δ₁) Γ₁ Δ₂ A =
    cong (⊗c Γ₁ (Γ ++ Δ₁ ++ I ∷ A ∷ Δ₂)) (let⊗-Ic21 b Γ₁ Δ₁  f g)
  let⊗-Ic21 b {T₁} Γ₁ Δ₁ {Δ₂} {A = A} (⊗c Γ Δ {J} {J'} f) g
    rewrite cases++-inj₂ (J ⊗ J' ∷ Δ ++ Δ₁) (Γ₁ ++ asCxt b T₁ Γ) Δ₂ A =
    cong (⊗c (Γ₁ ++ asCxt b T₁ Γ) (Δ ++ Δ₁ ++ I ∷ A ∷ Δ₂)) (let⊗-Ic21 b Γ₁ Δ₁ f g)
  
  let⊗-Ic22 b Γ₁ Δ₁ {Δ₂} {A = A} {J} {J'} ax g
    rewrite cases++-inj₁ Δ₁ Δ₂ (J ⊗ J' ∷ Γ₁) A = refl
  let⊗-Ic22 false Γ₁ Δ₁ (uf f) g = let⊗-Ic22 _ Γ₁ Δ₁ f g
  let⊗-Ic22 true Γ₁ Δ₁ {Δ₂} (uf {Γ = Γ} f) g =
    trans (cong (λ x → Ic (Δ₁ ++ I ∷ _ ∷ Δ₂) (Γ ++ Γ₁) x refl) (let⊗-Ic22 true Γ₁ Δ₁ f g) )
      (sym (IcIc Δ₁ Δ₂ (Γ ++ Γ₁) (let⊗ true (Δ₁ ++ _ ∷ Δ₂) Γ₁ f g) refl))
  let⊗-Ic22 b Γ₁ Δ₁ {Δ₂} (⊗r f f₁) g =
    trans (cong (λ x → ccut b (Δ₁ ++ I ∷ _ ∷ Δ₂) f x refl) (ccut-Ic22 false Δ₁ (Δ₂ ++ _ ∷ []) f₁ g refl))
      (ccut-Ic22 b Δ₁ Δ₂ f (ccut false (Δ₁ ++ _ ∷ Δ₂ ++ _ ∷ []) f₁ g refl) refl)
  let⊗-Ic22 b Γ₁ Δ₁ (Il f) g = let⊗-Ic22 _ Γ₁ Δ₁  f g
  let⊗-Ic22 b Γ₁ Δ₁ {Δ₂} {Γ} {A} (⊗l {A = A₁} {B} f) g
    rewrite cases++-inj₁ Δ₁ Δ₂ (A₁ ⊗ B ∷ Γ ++ Γ₁) A =
    cong (⊗c (Δ₁ ++ I ∷ A ∷ Δ₂) (Γ ++ Γ₁)) (let⊗-Ic22 b Γ₁ Δ₁  f g)
  let⊗-Ic22 b {T₁} Γ₁ Δ₁ {Δ₂} {A = A} (⊗c Γ Δ {J} {J'} f) g
    rewrite cases++-inj₁ Δ₁ (Δ₂ ++ asCxt b T₁ Γ) (J ⊗ J' ∷ Δ ++ Γ₁) A =
    cong (⊗c (Δ₁ ++ I ∷ A ∷ Δ₂ ++ asCxt b T₁ Γ) (Δ ++ Γ₁)) (let⊗-Ic22 b Γ₁ Δ₁ f g)
  
  let⊗-Ic1 b Γ Γ₁ Δ Λ ax g eq = ⊥-elim ([]disj∷ Γ eq)
  let⊗-Ic1 b Γ Γ₁ Δ Λ (uf f) g eq with cases∷ Γ eq
  let⊗-Ic1 false .[] Γ₁ Δ Λ (uf f) g refl | inj₁ (refl , refl , refl) =
    cong (λ x → Ic Γ₁ (Λ ++ Δ) x refl) (let⊗-bool Γ₁ Δ f g)
  let⊗-Ic1 true .[] Γ₁ Δ Λ (uf f) g refl | inj₁ (refl , refl , refl) =
    IcIc2 Γ₁ (Λ ++ Δ) (let⊗ true Γ₁ Δ f g) refl
  let⊗-Ic1 false .(_ ∷ Γ₀) Γ₁ Δ Λ (uf f) g refl | inj₂ (Γ₀ , refl , refl) = let⊗-Ic1 false Γ₀ Γ₁ Δ Λ f g refl
  let⊗-Ic1 true .(_ ∷ Γ₀) Γ₁ Δ Λ (uf f) g refl | inj₂ (Γ₀ , refl , refl) =
    trans (cong (λ x → Ic Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ ++ Δ) x refl) (let⊗-Ic1 true Γ₀ Γ₁ Δ Λ f g refl))
      (IcIc Γ₁ Γ₀ (Λ ++ Δ) (let⊗ true Γ₁ Δ f g) refl)
  let⊗-Ic1 b Γ Γ₁ Δ Λ (⊗r {Γ = Γ₂} {Δ₁} f f₁) g eq with cases++ Γ Γ₂ Λ Δ₁ eq
  let⊗-Ic1 b Γ Γ₁ Δ .(Γ₀ ++ Δ₁) (⊗r {Γ = .(Γ ++ _ ∷ Γ₀)} {Δ₁} f f₁) g refl | inj₁ (Γ₀ , refl , refl) =
    ccut-Ic1 b Γ₁ Γ Γ₀ f (ccut false (Γ₁ ++ _ ∷ []) f₁ g refl) refl
  let⊗-Ic1 b .(Γ₂ ++ Γ₀) Γ₁ Δ Λ (⊗r {Γ = Γ₂} {.(Γ₀ ++ _ ∷ Λ)} f f₁) g refl | inj₂ (Γ₀ , refl , refl) =
    trans (cong (λ x → ccut b Γ₁ f x refl) (ccut-Ic1 false (Γ₁ ++ _ ∷ []) Γ₀ Λ f₁ g refl))
      (ccut-Ic21 b Γ₁ Γ₀ f  (ccut false (Γ₁ ++ _ ∷ []) f₁ g refl) refl)
  let⊗-Ic1 b Γ Γ₁ Δ Λ (Il f) g refl = let⊗-Ic1 _ Γ Γ₁ Δ Λ f g refl
  let⊗-Ic1 b Γ Γ₁ Δ Λ {A = A} (⊗l {A = A₁} {B} f) g refl
    rewrite cases++-inj₂ (A₁ ⊗ B ∷ Γ) Γ₁ (Λ ++ Δ) A =
    cong (⊗c Γ₁ (Γ ++ I ∷ A ∷ Λ ++ Δ)) (let⊗-Ic1 b (_ ∷ Γ) Γ₁ Δ Λ f g refl)
  let⊗-Ic1 b Γ Γ₁ Δ Λ (⊗c Γ₂ Δ₁ {J} {J'} f) g eq with cases++ Γ Γ₂ Λ (J ⊗ J' ∷ Δ₁) eq
  let⊗-Ic1 b {T₁} Γ Γ₁ Δ .(Γ₀ ++ J ⊗ J' ∷ Δ₁) {A = A} (⊗c .(Γ ++ A ∷ Γ₀) Δ₁ {J} {J'} f) g refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ (Γ₁ ++ asCxt b T₁ Γ) Γ₀ (J ⊗ J' ∷ Δ₁ ++ Δ) A =
    cong (⊗c (Γ₁ ++ asCxt b T₁ Γ ++ I ∷ A ∷ Γ₀) (Δ₁ ++ Δ)) (let⊗-Ic1 _ Γ Γ₁ Δ (Γ₀ ++ J ∷ J' ∷ Δ₁) f g refl)
  let⊗-Ic1 b {T₁} .Γ₂ Γ₁ Δ .Δ₁ (⊗c Γ₂ Δ₁ {J} {J'} f) g refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] (Γ₁ ++ asCxt b T₁ Γ₂) (Δ₁ ++ Δ) (J ⊗ J') =
    cong (⊗c (Γ₁ ++ asCxt b T₁ Γ₂ ++ I ∷ []) (Δ₁ ++ Δ)) (let⊗-Ic1 _ Γ₂ Γ₁ Δ (J' ∷ Δ₁) f g refl)
  let⊗-Ic1 b {T₁} .(Γ₂ ++ J ⊗ J' ∷ Γ₀) Γ₁ Δ Λ {A = A} (⊗c Γ₂ .(Γ₀ ++ A ∷ Λ) {J} {J'} f) g refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Γ₁ ++ asCxt b T₁ Γ₂) (Λ ++ Δ) A =
    cong (⊗c (Γ₁ ++ asCxt b T₁ Γ₂) (Γ₀ ++ I ∷ A ∷ Λ ++ Δ)) (let⊗-Ic1 _ (Γ₂ ++ J ∷ J' ∷ Γ₀) Γ₁ Δ Λ f g refl)
  
  ccut-Ic1 b Δ₀ Γ Λ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic1 b Δ₀ Γ Λ f (uf g) eq with cases∷ Δ₀ eq
  ccut-Ic1 b {just x} .[] Γ Λ f (uf g) refl | inj₁ (refl , refl , refl) =
    cong uf (scut-Ic1 Γ Λ f g refl)
  ccut-Ic1 false {nothing} .[] Γ Λ f (uf g) refl | inj₁ (refl , refl , refl) =
    scut-Ic1 Γ Λ f g refl
  ccut-Ic1 true {nothing} .[] Γ Λ f (uf g) refl | inj₁ (refl , refl , refl) =
    cong uf (cong Il (scut-Ic1 Γ Λ f g refl))
  ccut-Ic1 b .(_ ∷ Γ₀) Γ Λ f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
    cong uf (ccut-Ic1 b Γ₀ Γ Λ f g refl)
  ccut-Ic1 b Δ₀ Γ Λ f Ir eq = ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic1 b Δ₀ Γ Λ {Δ'} f (⊗r {Γ = Γ₁} {Δ} g g₁) eq with cases++ Δ₀ Γ₁ Δ' Δ eq
  ccut-Ic1 b {T} Δ₀ Γ Λ {.(Γ₀ ++ Δ)} {B = B} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ (Δ₀ ++ asCxt b T Γ) (Λ ++ Γ₀) Δ B =
    cong₂ (⊗r {Γ = Δ₀ ++ asCxt b T Γ ++ _ ∷ _ ∷ Λ ++ Γ₀}{Δ}) (ccut-Ic1 b Δ₀ Γ Λ f g refl) refl
  ccut-Ic1 b {T} .(Γ₁ ++ Γ₀) Γ Λ {Δ'} {B = B} f (⊗r {Γ = Γ₁} {.(Γ₀ ++ _ ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ (Γ₀ ++ asCxt b T Γ) Γ₁ (Λ ++ Δ') B = cong₂ (⊗r {Γ = Γ₁}) refl (ccut-Ic1 b Γ₀ Γ Λ f g₁ refl)
  ccut-Ic1 b Δ₀ Γ Λ f (Il g) eq = cong Il (ccut-Ic1 b Δ₀ Γ Λ f g eq)
  ccut-Ic1 b Δ₀ Γ Λ f (⊗l g) refl = cong ⊗l (ccut-Ic1 b (_ ∷ Δ₀) Γ Λ f g refl)
  ccut-Ic1 b Δ₀ Γ Λ {Δ'} {B = B} f (⊗c Γ₁ Δ {J} {J'} g) eq with cases++ Δ₀ Γ₁ Δ' (J ⊗ J' ∷ Δ) eq
  ccut-Ic1 b {T} Δ₀ Γ Λ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} {B = B} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ (Δ₀ ++ asCxt b T Γ) (Λ ++ Γ₀) (J ⊗ J' ∷ Δ) B =
    cong (⊗c (Δ₀ ++ asCxt b T Γ ++ I ∷ B ∷ Λ ++ Γ₀) Δ) (ccut-Ic1 b Δ₀ Γ Λ f g refl)
  ccut-Ic1 b .Γ₁ Γ Λ {.Δ} {B = B} f (⊗c Γ₁ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl) = let⊗-Ic1 b Γ Γ₁ Δ Λ f g refl
  ccut-Ic1 b {T} .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Γ Λ {Δ'} {B = B} f (⊗c Γ₁ .(Γ₀ ++ _ ∷ Δ') {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀ ++ asCxt b T Γ) Γ₁ (Λ ++ Δ') B =
    cong (⊗c Γ₁ (Γ₀ ++ asCxt b T Γ ++ I ∷ B ∷ Λ ++ Δ')) (ccut-Ic1 b (Γ₁ ++ J ∷ J' ∷ Γ₀) Γ Λ f g refl)
  
  scut-Ic2 Γ Λ ax g refl = refl
  scut-Ic2 Γ Λ (uf f) g refl = cong uf (scut-Ic2 Γ Λ f g refl)
  scut-Ic2 Γ Λ Ir ax eq = ⊥-elim ([]disj∷ Γ eq)
  scut-Ic2 Γ Λ Ir (⊗r {Γ = Γ₁} {Δ} g g₁) eq with  cases++ Γ Γ₁ Λ Δ eq
  scut-Ic2 Γ .(Γ₀ ++ Δ) {A = A} Ir (⊗r {Γ = .(Γ ++ A ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀ Δ A = cong₂ (⊗r {Γ = Γ ++ _ ∷ _ ∷ Γ₀}{Δ}) (scut-Ic2 Γ Γ₀ Ir g refl) refl
  scut-Ic2 .(Γ₁ ++ Γ₀) Λ {A = A} Ir (⊗r {Γ = Γ₁} {.(Γ₀ ++ A ∷ Λ)} g g₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ₁ Λ A = refl
  scut-Ic2 Γ Λ Ir (Il g) refl = refl
  scut-Ic2 Γ Λ {A = A} Ir (⊗c Γ₁ Δ {J} {J'} g) eq with  cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Δ) eq
  scut-Ic2 Γ .(Γ₀ ++ J ⊗ J' ∷ Δ) {A = A} Ir (⊗c .(Γ ++ A ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀ (J ⊗ J' ∷ Δ) A = cong (⊗c (Γ ++ I ∷ A ∷ Γ₀) Δ) (scut-Ic2 Γ (Γ₀ ++ J ∷ J' ∷ Δ) Ir g refl)
  scut-Ic2 .Γ₁ .Δ {A = .(J ⊗ J')} Ir (⊗c Γ₁ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ₁ Δ (J ⊗ J') = cong (⊗c (Γ₁ ++ I ∷ []) Δ) (scut-Ic2 Γ₁ (J' ∷ Δ) Ir g refl)
  scut-Ic2 .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ {A = A} Ir (⊗c Γ₁ .(Γ₀ ++ A ∷ Λ) {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ₁ Λ A = cong (⊗c Γ₁ (Γ₀ ++ I ∷ A ∷ Λ)) (scut-Ic2 (Γ₁ ++ J ∷ J' ∷ Γ₀) Λ Ir g refl)
  scut-Ic2 Γ Λ (⊗r f f₁) ax eq = ⊥-elim ([]disj∷ Γ eq)
  scut-Ic2 Γ Λ (⊗r f f₁) (⊗r {Γ = Γ₁} {Δ} g g₁) eq with cases++ Γ Γ₁ Λ Δ eq
  scut-Ic2 Γ .(Γ₀ ++ Δ) {A = A} (⊗r {Γ = Γ₁}{Δ₁} f f₁) (⊗r {Γ = .(Γ ++ A ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ (Γ₁ ++ Δ₁ ++ Γ) Γ₀ Δ A = cong₂ (⊗r {Γ = Γ₁ ++ Δ₁ ++ Γ ++ _ ∷ _ ∷ Γ₀} {Δ}) (scut-Ic2 Γ Γ₀ (⊗r f f₁) g refl) refl
  scut-Ic2 .(Γ₁ ++ Γ₀) Λ {A = A} (⊗r {Γ = Γ} {Δ} f f₁) (⊗r {Γ = Γ₁} {.(Γ₀ ++ A ∷ Λ)} g g₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀  (Γ ++ Δ ++ Γ₁) Λ A = refl
  scut-Ic2 Γ Λ (⊗r {Γ = Γ₁} {Δ} f f₁) (⊗l g) refl =
    trans (cong (scut f) (ccut-Ic21 false [] Γ f₁ g refl ))
      (scut-Ic2 (Δ ++ Γ) Λ f (ccut false [] f₁ g refl) refl)
  scut-Ic2 Γ Λ (⊗r f f₁) (⊗c Γ₁ Δ {J} {J'} g) eq with  cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Δ) eq
  scut-Ic2 Γ .(Γ₀ ++ J ⊗ J' ∷ Δ)  {A = A} (⊗r {Γ = Γ₁}{Δ₁} f f₁) (⊗c .(Γ ++ _ ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ (Γ₁ ++ Δ₁ ++ Γ) Γ₀ (J ⊗ J' ∷ Δ) A =
      cong (⊗c (Γ₁ ++ Δ₁ ++ Γ ++ I ∷ A ∷ Γ₀) Δ) (scut-Ic2 Γ (Γ₀ ++ J ∷ J' ∷ Δ) (⊗r f f₁) g refl )
  scut-Ic2 .Γ₁ .Δ {A = .(J ⊗ J')} (⊗r {Γ = Γ} {Δ₁} f f₁) (⊗c Γ₁ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ []  (Γ ++ Δ₁ ++ Γ₁) Δ (J ⊗ J') =
    cong (⊗c (Γ ++ Δ₁ ++ Γ₁ ++ I ∷ []) Δ) (scut-Ic2 Γ₁ (J' ∷ Δ) (⊗r f f₁) g refl)
  scut-Ic2 .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ {A = A} (⊗r {Γ = Γ} {Δ} f f₁) (⊗c Γ₁ .(Γ₀ ++ A ∷ Λ) {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Γ ++ Δ ++ Γ₁) Λ A =
    cong (⊗c (Γ ++ Δ ++ Γ₁) (Γ₀ ++ I ∷ A ∷ Λ)) (scut-Ic2 (Γ₁ ++ J ∷ J' ∷ Γ₀) Λ (⊗r f f₁) g refl)
  scut-Ic2 Γ Λ (Il f) g eq = cong Il (scut-Ic2 Γ Λ f g eq)
  scut-Ic2 Γ Λ (⊗l f) g refl = cong ⊗l (scut-Ic2 Γ Λ f g refl)
  scut-Ic2 Γ Λ {A = A} (⊗c Γ₁ Δ {J} {J'} f) g refl
    rewrite cases++-inj₂ (J ⊗ J' ∷ Δ ++ Γ) Γ₁ Λ A  =
    cong (⊗c Γ₁ (Δ ++ Γ ++ I ∷ A ∷ Λ)) (scut-Ic2 Γ Λ f g refl)
  
  scut-Ic1 Γ Λ ax g eq = ⊥-elim ([]disj∷ Γ eq)
  scut-Ic1 Γ Λ (uf f) g eq with cases∷ Γ eq
  scut-Ic1 .[] Λ (uf f) g refl | inj₁ (refl , refl , refl) = refl
  scut-Ic1 .(_ ∷ Γ₀) Λ (uf f) g refl | inj₂ (Γ₀ , refl , refl) = cong uf (scut-Ic1 Γ₀ Λ f g refl)
  scut-Ic1 Γ Λ Ir g eq = ⊥-elim ([]disj∷ Γ eq)
  scut-Ic1 Γ Λ (⊗r {Γ = Γ₁} {Δ} f f₁) g eq with cases++ Γ Γ₁ Λ Δ eq
  scut-Ic1 Γ .(Γ₀ ++ Δ) {A = A} (⊗r {Γ = .(Γ ++ A ∷ Γ₀)} {Δ} f f₁) ax refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀ Δ A = refl
  scut-Ic1 Γ .(Γ₀ ++ Δ) {A = A} (⊗r {Γ = .(Γ ++ A ∷ Γ₀)} {Δ} f f₁) (⊗r {Γ = Γ₁} {Δ₁} g g₁) refl | inj₁ (Γ₀ , refl , refl) with scut-Ic1 Γ (Γ₀ ++ Δ) (⊗r f f₁) g refl
  ... | ih
    rewrite cases++-inj₁ Γ (Γ₀ ++ Δ ++ Γ₁) Δ₁ A | cases++-inj₁ Γ Γ₀ Δ A =
    cong₂ (⊗r {Γ = Γ ++ _ ∷ _ ∷ Γ₀ ++ Δ ++ Γ₁}{Δ₁}) ih refl 
  scut-Ic1 Γ .(Γ₀ ++ Δ) (⊗r {Γ = .(Γ ++ _ ∷ Γ₀)} {Δ} f f₁) (⊗l g) refl | inj₁ (Γ₀ , refl , refl) = scut-Ic1 Γ Γ₀ f (ccut false [] f₁ g refl) refl
  scut-Ic1 Γ .(Γ₀ ++ Δ) {A = A} (⊗r {Γ = .(Γ ++ A ∷ Γ₀)} {Δ} f f₁) (⊗c Γ₁ Δ₁ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl) with scut-Ic1 Γ (Γ₀ ++ Δ) (⊗r f f₁) g refl
  ... | ih 
    rewrite cases++-inj₁ Γ (Γ₀ ++ Δ ++ Γ₁) (J ⊗ J' ∷ Δ₁) A | cases++-inj₁ Γ Γ₀ Δ A =
    cong (⊗c (Γ ++ I ∷ A ∷ Γ₀ ++ Δ ++ Γ₁) Δ₁) ih
  scut-Ic1 .(Γ₁ ++ Γ₀) Λ {A = A} (⊗r {Γ = Γ₁} {.(Γ₀ ++ A ∷ Λ)} f f₁) ax refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ₁ Λ A = refl
  scut-Ic1 .(Γ₁ ++ Γ₀) Λ {A = A} (⊗r {Γ = Γ₁} {.(Γ₀ ++ A ∷ Λ)} f f₁) (⊗r {Γ = Γ} {Δ} g g₁) refl | inj₂ (Γ₀ , refl , refl) with scut-Ic1 (Γ₁ ++ Γ₀) Λ (⊗r f f₁) g refl
  ... | ih 
    rewrite cases++-inj₁ (Γ₁ ++ Γ₀) (Λ ++ Γ) Δ A | cases++-inj₂ Γ₀ Γ₁ Λ A = cong₂ (⊗r {Γ = Γ₁ ++ Γ₀ ++ _ ∷ _ ∷ Λ ++ Γ}{Δ}) ih refl
  scut-Ic1 .(Γ₁ ++ Γ₀) Λ (⊗r {Γ = Γ₁} {.(Γ₀ ++ _ ∷ Λ)} f f₁) (⊗l {Γ = Δ} g) refl | inj₂ (Γ₀ , refl , refl) =
    trans (cong (scut f) (ccut-Ic1 false [] Γ₀ Λ f₁ g refl))
      (scut-Ic2 Γ₀ (Λ ++ Δ) f  (ccut false [] f₁ g refl) refl)
  scut-Ic1 .(Γ₁ ++ Γ₀) Λ {A = A} (⊗r {Γ = Γ₁} {.(Γ₀ ++ A ∷ Λ)} f f₁) (⊗c Γ Δ {J} {J'} g) refl | inj₂ (Γ₀ , refl , refl) with scut-Ic1 (Γ₁ ++ Γ₀) Λ (⊗r f f₁) g refl
  ... | ih 
    rewrite cases++-inj₁ (Γ₁ ++ Γ₀) (Λ ++ Γ) (J ⊗ J' ∷ Δ) A | cases++-inj₂ Γ₀ Γ₁ Λ A =
    cong (⊗c (Γ₁ ++ Γ₀ ++ I ∷ A ∷ Λ ++ Γ) Δ) ih
  scut-Ic1 Γ Λ (Il f) g eq = cong Il (scut-Ic1 Γ Λ f g eq)
  scut-Ic1 Γ Λ (⊗l f) g refl = cong ⊗l (scut-Ic1 (_ ∷ Γ) Λ f g refl)
  scut-Ic1 Γ Λ {A = A} (⊗c Γ₁ Δ {J} {J'} f) g eq with cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Δ) eq
  scut-Ic1 Γ .(Γ₀ ++ J ⊗ J' ∷ Δ) {Δ = Δ₁} {A = A} (⊗c .(Γ ++ A ∷ Γ₀) Δ {J} {J'} f) g refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀ (J ⊗ J' ∷ Δ ++ Δ₁) A = cong (⊗c (Γ ++ I ∷ A ∷ Γ₀) (Δ ++ Δ₁)) (scut-Ic1 Γ (Γ₀ ++ J ∷ J' ∷ Δ) f g refl)
  scut-Ic1 .Γ₁ .Δ {Δ = Δ₁} {A = .(J ⊗ J')} (⊗c Γ₁ Δ {J} {J'} f) g refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ₁ (Δ ++ Δ₁) (J ⊗ J') = cong (⊗c (Γ₁ ++ I ∷ []) (Δ ++ Δ₁)) (scut-Ic1 Γ₁ (J' ∷ Δ) f g refl)
  scut-Ic1 .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ {Δ = Δ₁} {A = A} (⊗c Γ₁ .(Γ₀ ++ A ∷ Λ) {J} {J'} f) g refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ₁ (Λ ++ Δ₁) A = cong (⊗c Γ₁ (Γ₀ ++ I ∷ A ∷ Λ ++ Δ₁)) (scut-Ic1 (Γ₁ ++ J ∷ J' ∷ Γ₀) Λ f g refl)

abstract
  scut-par-ccut : {b : Bool}{S T : Stp}{Γ₁ Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₂ C : Fma}
    → (f₁ : T ∣ Γ₁ ⊢ A₁)(f₂ : S ∣ Γ₂ ⊢ A₂)(g : just A₁ ∣ Δ ⊢ C)
    → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
    → scut f₁ (ccut b Δ₀ f₂ g r) ≡ ccut b (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_++_ Γ₁) r)
  scut⊗r-let⊗ : ∀{b S T Γ₁ Δ₁ Γ₂ Γ Δ A B C J J'}
    → (f₁ : T ∣ Γ₁ ⊢ A) (f₃ : nothing ∣ Δ₁ ⊢ B) (f₂ : S ∣ Γ₂ ⊢ J ⊗ J') (g  : just (A ⊗ B) ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C)
    → scut (⊗r f₁ f₃) (let⊗ b Γ Δ f₂ g) ≡  let⊗ b (Γ₁ ++ Δ₁ ++ Γ) Δ f₂ (scut (⊗r f₁ f₃) g)
  ccut-par-ccut : {b b' : Bool} {S₁ S₂ T : Stp} → {Γ₁ Γ₂ : Cxt} → (Δ₀ : Cxt) → {Δ Δ₁ Δ₂ : Cxt} → {A₁ A₂ C : Fma}
    → (f₁ : S₁ ∣ Γ₁ ⊢ A₁)(f₂ : S₂ ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
    → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
    → ccut b' Δ₀ f₁ (ccut b (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) refl ≡ ccut b (Δ₀ ++ asCxt b' S₁ Γ₁ ++ Δ₁) f₂ (ccut b' Δ₀ f₁ g r) refl
  let⊗-par-ccut1 : ∀{b b'}{S₁ S₂ T Γ₁ Γ₂} Δ₀ {Δ₁ Δ₂ A C J J'}
    → (f₁ : S₁ ∣ Γ₁ ⊢ J ⊗ J')(f₂ : S₂ ∣ Γ₂ ⊢ A)(g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ++ A ∷ Δ₂ ⊢ C)
    → let⊗ b Δ₀ (Δ₁ ++ asCxt b' S₂ Γ₂ ++ Δ₂) f₁ (ccut b' (Δ₀ ++ J ∷ J' ∷ Δ₁) f₂ g refl)
           ≡ ccut b' (Δ₀ ++ asCxt b S₁ Γ₁ ++ Δ₁) f₂ (let⊗ b Δ₀ (Δ₁ ++ A ∷ Δ₂) f₁ g) refl
  let⊗-par-ccut2 : ∀{b b'}{S₁ S₂ T Γ₁ Γ₂} Δ₀ {Δ₁ Δ₂ A C J J'} 
    → (f₁ : S₁ ∣ Γ₁ ⊢ A)(f₂ : S₂ ∣ Γ₂ ⊢ J ⊗ J')(g : T ∣ Δ₀ ++ A ∷ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)
    → let⊗ b' (Δ₀ ++ asCxt b S₁ Γ₁ ++ Δ₁) Δ₂ f₂ (ccut b Δ₀ f₁ g refl)
           ≡ ccut b Δ₀ f₁ (let⊗ b' (Δ₀ ++ A ∷ Δ₁) Δ₂ f₂ g) refl

  scut-par-ccut Δ₀ ax f₂ g refl = refl
  scut-par-ccut Δ₀ (uf f₁) f₂ g refl = cong uf (scut-par-ccut Δ₀ f₁ f₂ g refl)
  scut-par-ccut Δ₀ Ir f₂ g refl =
    begin
    scut Ir (ccut _ Δ₀ f₂ g refl)
    ≡⟨ sym (Il-1-scutIr (ccut _ Δ₀ f₂ g refl)) ⟩
    Il-1 (ccut _ Δ₀ f₂ g refl)
    ≡⟨ ccut-Il-1 Δ₀ f₂ g refl ⟩
    ccut _ Δ₀ f₂ (Il-1 g) refl
    ≡⟨ cong (λ x → ccut _ Δ₀ f₂ x refl) (Il-1-scutIr g) ⟩
    ccut _ Δ₀ f₂ (scut Ir g) refl
    ∎
  scut-par-ccut Δ₀ (⊗r f₁ f₃) f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
  scut-par-ccut Δ₀ {Δ'} (⊗r f₁ f₃) f₂ (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
  scut-par-ccut {b}{S}{Γ₂ = Γ₂} Δ₀ {.(Γ₀ ++ Δ)} {A₂ = A₂} (⊗r {Γ = Γ} {Δ₁} f₁ f₃) f₂ (⊗r {Γ = .(Δ₀ ++ A₂ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ (Γ ++ Δ₁ ++ Δ₀) Γ₀ Δ A₂ =
    cong₂ (⊗r {Γ = Γ ++ Δ₁ ++ Δ₀ ++ asCxt b S Γ₂ ++ Γ₀}{Δ}) (scut-par-ccut Δ₀ (⊗r f₁ f₃) f₂ g refl ) refl
  scut-par-ccut {Γ₂ = Γ₂} .(Γ ++ Γ₀) {Δ'} {A₂ = A₂} (⊗r {Γ = Γ₁} {Δ} f₁ f₃) f₂ (⊗r {Γ = Γ} {.(Γ₀ ++ A₂ ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ (Γ₁ ++ Δ ++ Γ) Δ' A₂ = refl
  scut-par-ccut Δ₀ (⊗r {Γ = Γ}{Δ} f₁ f₁') f₂ (⊗l {B = B} g) refl =
    begin
    scut f₁ (ccut false [] f₁' (ccut _ (B ∷ Δ₀) f₂ g refl) refl)
    ≡⟨ cong (scut f₁) (ccut-par-ccut [] f₁' f₂ g refl) ⟩ 
    scut f₁ (ccut _ (Δ ++ Δ₀) f₂ (ccut false [] f₁' g refl) refl)
    ≡⟨ scut-par-ccut (Δ ++ Δ₀) f₁ f₂ (ccut _ [] f₁' g refl) refl ⟩
     ccut _ (Γ ++ Δ ++ Δ₀) f₂ (scut f₁ (ccut false [] f₁' g refl)) refl
    ∎
  scut-par-ccut Δ₀ {Δ'} (⊗r f₁ f₃) f₂ (⊗c Γ Δ {J}{J'} g) r with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) r
  scut-par-ccut {b}{S}{Γ₂ = Γ₂} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} {A₂ = A₂} (⊗r {Γ = Γ} {Δ₁} f₁ f₃) f₂ (⊗c .(Δ₀ ++ A₂ ∷ Γ₀) Δ {J}{J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ (Γ ++ Δ₁ ++ Δ₀) Γ₀ (J ⊗ J' ∷ Δ) A₂ = cong (⊗c (Γ ++ Δ₁ ++ Δ₀ ++ asCxt b S Γ₂ ++ Γ₀) Δ) (scut-par-ccut Δ₀ (⊗r f₁ f₃) f₂ g refl)
  scut-par-ccut {Γ₂ = Γ₂} .Γ {.Δ} (⊗r {Γ = Γ₁} {Δ₁} f₁ f₃) f₂ (⊗c Γ Δ {J}{J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] (Γ₁ ++ Δ₁ ++ Γ) Δ (J ⊗ J') = scut⊗r-let⊗ f₁ f₃ f₂ g 
  scut-par-ccut {b}{S}{Γ₂ = Γ₂} .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} {A₂ = A₂} (⊗r {Γ = Γ₁} {Δ} f₁ f₃) f₂ (⊗c Γ .(Γ₀ ++ A₂ ∷ Δ') {J}{J'} g) refl | inj₂ (._ ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Γ₁ ++ Δ ++ Γ) Δ' A₂ = cong (⊗c (Γ₁ ++ Δ ++ Γ) (Γ₀ ++ asCxt b S Γ₂ ++ Δ')) (scut-par-ccut (Γ ++ J ∷ J' ∷ Γ₀) (⊗r f₁ f₃) f₂ g refl)
  scut-par-ccut {b}{S}{Γ₂ = Γ₂} Δ₀ {Δ'} {A₂ = A₂} (⊗c Γ Δ {J} {J'} f₁) f₂ g refl
    rewrite cases++-inj₂ (J ⊗ J' ∷ Δ ++ Δ₀) Γ Δ' A₂ = cong (⊗c Γ (Δ ++ Δ₀ ++ asCxt b S Γ₂ ++ Δ')) (scut-par-ccut Δ₀ f₁ f₂ g refl)
  scut-par-ccut Δ₀ (Il f₁) f₂ g refl = cong Il (scut-par-ccut Δ₀ f₁ f₂ g refl)
  scut-par-ccut Δ₀ (⊗l f₁) f₂ g refl = cong ⊗l (scut-par-ccut Δ₀ f₁ f₂ g refl)

  scut⊗r-let⊗ {false} f₁ f₃ (uf f₂) g = scut⊗r-let⊗ f₁ f₃ f₂ g
  scut⊗r-let⊗ {true} {Γ₁ = Γ₂} {Δ₁} {Γ = Γ} {Δ} f₁ f₃ (uf {Γ₁} f₂) g = 
   trans (scut-Ic2 Γ (Γ₁ ++ Δ) (⊗r f₁ f₃) (let⊗ true Γ Δ f₂ g) refl)
     (cong (λ x → Ic (Γ₂ ++ Δ₁ ++ Γ) (Γ₁ ++ Δ) x refl) (scut⊗r-let⊗ f₁ f₃ f₂ g)) 
  scut⊗r-let⊗ {b}{S} {Γ₁ = Γ₁} {Δ₁} {Γ = Γ₂} {Δ₂} f₁ f₃ (⊗c Γ Δ f₂) g =
    cong (⊗c (Γ₁ ++ Δ₁ ++ Γ₂ ++ asCxt b S Γ) (Δ ++ Δ₂)) (scut⊗r-let⊗ f₁ f₃ f₂ g)
  scut⊗r-let⊗ f₁ f₃ ax g = refl
  scut⊗r-let⊗ {b}{Γ₁ = Γ₁}{Δ₁}{Γ = Γ} f₁ f₃ (⊗r f₂ f₂') g =
    trans (scut-par-ccut Γ (⊗r f₁ f₃) f₂ (ccut false (Γ ++ _ ∷ []) f₂' g refl) refl)
      (cong (λ x → ccut b (Γ₁ ++ Δ₁ ++ Γ) f₂ x refl) (scut-par-ccut (Γ ++ _ ∷ []) (⊗r f₁ f₃) f₂' g refl))
  scut⊗r-let⊗ f₁ f₃ (Il f₂) g = scut⊗r-let⊗ f₁ f₃ f₂ g
  scut⊗r-let⊗ {Γ₁ = Γ₁} {Δ₁} {Γ₂} {Γ} {Δ} f₁ f₃ (⊗l f₂) g =
    cong (⊗c (Γ₁ ++ Δ₁ ++ Γ) (Γ₂ ++ Δ)) (scut⊗r-let⊗ f₁ f₃ f₂ g)

  ccut-par-ccut Δ₀ f₁ f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-par-ccut Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (uf g) r with cases∷ (Δ₀ ++ A₁ ∷ Δ₁) r
  ccut-par-ccut Δ₀ f₁ f₂ (uf g) r | inj₁ (p , q , s) = ⊥-elim ([]disj∷ Δ₀ (sym q))
  ccut-par-ccut Δ₀ f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , s) with cases∷ Δ₀ r
  ccut-par-ccut {b} {false} {nothing} .[] {.(_ ∷ Γ₀ ++ _ ∷ _)} {_} {_} {_} f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = scut-par-ccut Γ₀ f₁ f₂ g refl
  ccut-par-ccut {b} {true} {nothing} .[] {.(_ ∷ Γ₀ ++ _ ∷ _)} {_} {_} {_} f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = cong uf (cong Il (scut-par-ccut Γ₀ f₁ f₂ g refl))
  ccut-par-ccut {_}{b'}{just x} .[] {.(_ ∷ Γ₀ ++ _ ∷ _)} {_} {_} {_} f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = cong uf (scut-par-ccut Γ₀ f₁ f₂ g refl)  
  ccut-par-ccut .(_ ∷ Δ₀) f₁ f₂ (uf g) r | inj₂ (._ , refl , refl) | inj₂ (Δ₀ , refl , refl) = cong uf (ccut-par-ccut Δ₀ f₁ f₂ g refl)
  ccut-par-ccut Δ₀ f₁ f₂ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ Δ r
  ccut-par-ccut {b}{b'}{S₁}{S₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀ ++ Δ)} {A₁} {A₂} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) Δ A₁ | cases++-inj₁ Δ₀ (Δ₁ ++ asCxt b S₂ Γ₂ ++ Γ₀) Δ A₁ | cases++-inj₁ (Δ₀ ++ asCxt b' S₁ Γ₁ ++ Δ₁) Γ₀ Δ A₂ =
    cong₂ (⊗r {Γ = Δ₀ ++ asCxt b' S₁ Γ₁ ++ Δ₁ ++ asCxt b S₂ Γ₂ ++ Γ₀}{Δ}) (ccut-par-ccut Δ₀ f₁ f₂ g refl) refl
  ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ₂)} g g₁) r | inj₂ (Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym q)
  ccut-par-ccut {b}{b'}{S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = ._} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r g g₁) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ asCxt b S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ Γ₀ (Δ₀ ++ asCxt b' S₁ Γ₁ ++ Γ₀') Δ₂ A₂ = refl
  ccut-par-ccut {b}{b'}{S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} ._ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁) refl | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , refl , refl)
    rewrite cases++-inj₂ Γ₀' Γ (Δ₁ ++ asCxt b S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₂ Γ₀' Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (Γ₀' ++ asCxt b' S₁ Γ₁ ++ Δ₁) Γ Δ₂ A₂ =
    cong (⊗r g) (ccut-par-ccut Γ₀' f₁ f₂ g₁ refl)
  ccut-par-ccut Δ₀ f₁ f₂ (Il g) refl = cong Il (ccut-par-ccut Δ₀ f₁ f₂ g refl)
  ccut-par-ccut Δ₀ f₁ f₂ (⊗l {B = B} g) refl = cong ⊗l (ccut-par-ccut (B ∷ Δ₀) f₁ f₂ g refl)
  ccut-par-ccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗c Γ Δ {J} {J'} g) r with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ (J ⊗ J' ∷ Δ) r
  ccut-par-ccut {b}{b'}{S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀ ++ J ⊗ J' ∷ Δ)} {A₁} {A₂} f₁ f₂ (⊗c .(Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Δ₁ ++ asCxt b S₂ Γ₂ ++ Γ₀) (J ⊗ J' ∷ Δ) A₁ | cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) (J ⊗ J' ∷ Δ) A₁ | cases++-inj₁ (Δ₀ ++ asCxt b' S₁ Γ₁ ++ Δ₁) Γ₀ (J ⊗ J' ∷ Δ) A₂ =
    cong (⊗c (Δ₀ ++ asCxt b' S₁ Γ₁ ++ Δ₁ ++ asCxt b S₂ Γ₂ ++ Γ₀) Δ) (ccut-par-ccut Δ₀ f₁ f₂ g refl)
  ccut-par-ccut {b}{b'}{S₁}{S₂}{Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.Δ} {A₁} {.(J ⊗ J')} f₁ f₂ (⊗c .(Δ₀ ++ A₁ ∷ Δ₁) Δ {J} {J'} g) refl | inj₂ ([] , refl , refl) 
    rewrite cases++-inj₁ Δ₀ Δ₁ (J ⊗ J' ∷ Δ) A₁ | cases++-inj₂ [] (Δ₀ ++ asCxt b' S₁ Γ₁ ++ Δ₁) Δ (J ⊗ J') = sym (let⊗-par-ccut2 Δ₀ f₁ f₂ g)
  ccut-par-ccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗c Γ .(Γ₀ ++ A₂ ∷ Δ₂) {J} {J'} g) r | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ (_ ∷ Γ₀) (sym q)
  ccut-par-ccut {b}{b'}{S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = ._} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗c ._ ._ {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Γ₀ ++ asCxt b S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Γ₀ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Δ₀ ++ asCxt b' S₁ Γ₁ ++ Γ₀') Δ₂ A₂
    = cong (⊗c (Δ₀ ++ asCxt b' S₁ Γ₁ ++ Γ₀') (Γ₀ ++ asCxt b S₂ Γ₂ ++ Δ₂)) (ccut-par-ccut {Γ₁ = Γ₁} Δ₀ {Δ₁ = Γ₀' ++ J ∷ J' ∷ Γ₀} f₁ f₂ g refl)
  ccut-par-ccut {b}{b'} {S₁}{S₂}{Γ₁ = Γ₁} {Γ₂} .Γ {Δ₁ = .Γ₀} {Δ₂} {.(J ⊗ J')} {A₂} f₁ f₂ (⊗c Γ ._ {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ (Γ₀ ++ asCxt b S₂ Γ₂ ++ Δ₂) (J ⊗ J') | cases++-inj₂ [] Γ (Γ₀ ++ A₂ ∷ Δ₂) (J ⊗ J') = let⊗-par-ccut1 Γ f₁ f₂ g
  ccut-par-ccut {b}{b'} {S₁}{S₂} {Γ₁ = Γ₁} {Γ₂} ._ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗c Γ ._ {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ ._ , refl , refl) | inj₂ (.(J ⊗ J') ∷ Γ₀' , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Δ₁ ++ asCxt b S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (J ⊗ J' ∷ Γ₀' ++ asCxt b' S₁ Γ₁ ++ Δ₁)  Γ Δ₂ A₂ =
    cong (⊗c Γ (Γ₀' ++ asCxt b' S₁ Γ₁ ++ Δ₁ ++ asCxt b S₂ Γ₂ ++ Δ₂)) (ccut-par-ccut (Γ ++ J ∷ J' ∷ Γ₀') f₁ f₂ g refl)

  let⊗-par-ccut1 Δ₀ {Δ₁ = Δ₁} {Δ₂} {A} {J = J} {J'} ax f₂ g
    rewrite cases++-inj₂ (J ⊗ J' ∷ Δ₁) Δ₀ Δ₂ A = refl
  let⊗-par-ccut1 {false} Δ₀ (uf f₁) f₂ g = let⊗-par-ccut1 Δ₀ f₁ f₂ g
  let⊗-par-ccut1 {true}{b'}{S₂ = S₂}{Γ₂ = Γ₂} Δ₀ {Δ₁}{Δ₂} (uf {Γ = Γ} f₁) f₂ g =
    trans (cong (λ x → Ic Δ₀ (Γ ++ Δ₁ ++ asCxt b' S₂ Γ₂ ++ Δ₂) x refl) (let⊗-par-ccut1 Δ₀ f₁ f₂ g))
      (sym (ccut-Ic22 b' Δ₀ (Γ ++ Δ₁) f₂ (let⊗ true Δ₀ (Δ₁ ++ _ ∷ Δ₂) f₁ g) refl))
  let⊗-par-ccut1 {b}{b'} Δ₀ {Δ₁} (⊗r {Δ = Δ} f₁ f₃) f₂ g =
    trans (cong (λ x → ccut b Δ₀ f₁ x refl) (ccut-par-ccut (Δ₀ ++ _ ∷ []) f₃ f₂ g refl))
      (ccut-par-ccut Δ₀ {_}{Δ ++ Δ₁} f₁ f₂ (ccut false (Δ₀ ++ _ ∷ []) f₃ g refl) refl) 
  let⊗-par-ccut1 Δ₀ (Il f₁) f₂ g = let⊗-par-ccut1 Δ₀ f₁ f₂ g
  let⊗-par-ccut1 {b}{b'}{S₂ = S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁} {Δ₂} {A₁} {J = J} {J'} (⊗l {A = A} {B} f₁) f₂ g
    rewrite cases++-inj₂ (A ⊗ B ∷ Γ₁ ++ Δ₁) Δ₀ Δ₂ A₁ =
    cong (⊗c Δ₀ (Γ₁ ++ Δ₁ ++ asCxt b' S₂ Γ₂ ++ Δ₂)) (let⊗-par-ccut1 Δ₀ f₁ f₂ g)
  let⊗-par-ccut1 {b}{b'}{S₁} {S₂} {Γ₂ = Γ₂} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} (⊗c Γ Δ {J₁} {J''} f₁) f₂ g
    rewrite cases++-inj₂ (J₁ ⊗ J'' ∷ Δ ++ Δ₁) (Δ₀ ++ asCxt b S₁ Γ) Δ₂ A =
    cong (⊗c (Δ₀ ++ asCxt b S₁ Γ) (Δ ++ Δ₁ ++ asCxt b' S₂ Γ₂ ++ Δ₂)) (let⊗-par-ccut1 Δ₀ f₁ f₂ g)
 
  let⊗-par-ccut2 Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} f₁ ax g
    rewrite cases++-inj₁ Δ₀ Δ₁ (J ⊗ J' ∷ Δ₂) A = refl
  let⊗-par-ccut2 {b' = false} Δ₀ f₁ (uf f₂) g = let⊗-par-ccut2 Δ₀ f₁ f₂ g
  let⊗-par-ccut2 {b} {true} {S₁} {Γ₁ = Γ₁} Δ₀ {Δ₁} {Δ₂} f₁ (uf {Γ} f₂) g =
    trans (cong (λ x → Ic (Δ₀ ++ asCxt b S₁ Γ₁ ++ Δ₁) (Γ ++ Δ₂) x refl) (let⊗-par-ccut2 Δ₀ f₁ f₂ g))
      (sym (ccut-Ic21 b Δ₀ Δ₁ f₁ (let⊗ true (Δ₀ ++ _ ∷ Δ₁) Δ₂ f₂ g) refl))
  let⊗-par-ccut2 {b}{b'}{S₁} {Γ₁ = Γ₁} Δ₀ {Δ₁} f₁ (⊗r f₂ f₃) g =
    trans (cong (λ x → ccut b' (Δ₀ ++ asCxt b S₁ Γ₁ ++ Δ₁) f₂ x refl) (sym (ccut-par-ccut Δ₀ {_}{Δ₁ ++ _ ∷ []} f₁ f₃ g refl)))
      (sym (ccut-par-ccut Δ₀ f₁ f₂ (ccut false (Δ₀ ++ _ ∷ Δ₁ ++ _ ∷ []) f₃ g refl) refl))
  let⊗-par-ccut2 Δ₀ f₁ (Il f₂) g = let⊗-par-ccut2 Δ₀ f₁ f₂ g
  let⊗-par-ccut2 {b}{b'} {S₁} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} f₁ (⊗l {A = A₁} {B} f₂) g
    rewrite cases++-inj₁ Δ₀ Δ₁ (A₁ ⊗ B ∷ Γ₂ ++ Δ₂) A =
    cong (⊗c (Δ₀ ++ asCxt b S₁ Γ₁ ++ Δ₁) (Γ₂ ++ Δ₂)) (let⊗-par-ccut2 Δ₀ f₁ f₂ g)
  let⊗-par-ccut2 {b}{b'}{S₁} {S₂} {Γ₁ = Γ₁} Δ₀ {Δ₁} {Δ₂} {A} {J = J} {J'} f₁ (⊗c Γ Δ {J₁} {J''} f₂) g 
    rewrite cases++-inj₁ Δ₀ (Δ₁ ++ asCxt b' S₂ Γ) (J₁ ⊗ J'' ∷ Δ ++ Δ₂) A =
    cong (⊗c (Δ₀ ++ asCxt b S₁ Γ₁ ++ Δ₁ ++ asCxt b' S₂ Γ) (Δ ++ Δ₂)) (let⊗-par-ccut2 Δ₀ f₁ f₂ g)



-- ====================================================================

abstract
  ccut-Ic2-n-false : {S : Stp} → {Δ Γ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
              (f : nothing ∣ Γ ⊢ A) (g : S ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ') →  
              ccut false (Δ₀ ++ I ∷ []) f (Ic Δ₀ Δ' g eq) refl ≡ ccut true Δ₀ f g eq
  let⊗-Ic2-n-false : {S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {C J J' : Fma}
      → (f : nothing ∣ Γ ⊢ J ⊗ J') (g : S ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
      → let⊗ false (Δ₀ ++ I ∷ []) Δ₁ f (Ic Δ₀ (J' ∷ Δ₁) g refl) ≡ let⊗ true Δ₀ Δ₁ f g
  let⊗-Ic2-j : {b : Bool} {S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {A C J J' : Fma}
      → (f : just A ∣ Γ ⊢ J ⊗ J') (g : S ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
      → let⊗ b (Δ₀ ++ I ∷ []) Δ₁ f (Ic Δ₀ (J' ∷ Δ₁) g refl) ≡ Ic Δ₀ (Γ ++ Δ₁) (let⊗ b Δ₀ Δ₁ f g) refl
  let⊗-Ic2-n-true : {S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {C J J' : Fma}
      → (f : nothing ∣ Γ ⊢ J ⊗ J') (g : S ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
      → let⊗ true (Δ₀ ++ I ∷ []) Δ₁ f (Ic Δ₀ (J' ∷ Δ₁) g refl) ≡ Ic Δ₀ (Γ ++ Δ₁) (let⊗ true Δ₀ Δ₁ f g) refl
  ccut-Ic2-n-true : {S : Stp} → {Δ Γ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
              (f : nothing ∣ Γ ⊢ A) (g : S ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ') →  
              ccut true (Δ₀ ++ I ∷ []) f (Ic Δ₀ Δ' g eq) refl ≡ Ic Δ₀ (Γ ++ Δ') (ccut true Δ₀ f g eq) refl 
  ccut-Ic2-j : {b : Bool} {S : Stp} → {Δ Γ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' C : Fma} → 
              (f : just A' ∣ Γ ⊢ A) (g : S ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ') →  
              ccut b (Δ₀ ++ I ∷ []) f (Ic Δ₀ Δ' g eq) refl ≡ Ic Δ₀ (Γ ++ Δ') (ccut b Δ₀ f g eq) refl 

  ccut-Ic2-n-false Δ₀ f ax eq =  ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic2-n-false Δ₀ f (uf g) eq with cases∷ Δ₀ eq
  ccut-Ic2-n-false .[] f (uf g) eq | inj₁ (refl , refl , refl) = refl
  ccut-Ic2-n-false .(_ ∷ Γ₀) f (uf g) eq | inj₂ (Γ₀ , refl , refl) =
    cong uf (ccut-Ic2-n-false Γ₀ f g refl)
  ccut-Ic2-n-false Δ₀ f Ir eq =  ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic2-n-false Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
  ccut-Ic2-n-false {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} {A = A} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ (Δ₀ ++ I ∷ []) Γ₀ Δ A =
    cong₂ (⊗r {Γ = Δ₀ ++ _ ∷ Γ ++ Γ₀} {Δ}) (ccut-Ic2-n-false Δ₀ f g refl) refl
  ccut-Ic2-n-false .(Γ ++ Γ₀) {Δ'} {A} f (⊗r {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ (Γ₀ ++ I ∷ []) Γ Δ' A = cong (⊗r g) (ccut-Ic2-n-false Γ₀ f g₁ refl)
  ccut-Ic2-n-false Δ₀ f (Il g) eq = cong Il (ccut-Ic2-n-false Δ₀ f g eq)
  ccut-Ic2-n-false Δ₀ f (⊗l g) refl = cong ⊗l (ccut-Ic2-n-false (_ ∷ Δ₀) f g refl)
  ccut-Ic2-n-false Δ₀ {Δ'} f (⊗c Γ Δ {J} {J'} g) eq with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) eq
  ccut-Ic2-n-false {Γ = Γ} Δ₀ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} {A} f (⊗c .(Δ₀ ++ A ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁  (Δ₀ ++ I ∷ []) Γ₀ (J ⊗ J' ∷ Δ) A =
    cong (⊗c (Δ₀ ++ I ∷ Γ ++ Γ₀) Δ) (ccut-Ic2-n-false Δ₀ f g refl)
  ccut-Ic2-n-false .Γ {.Δ} f (⊗c Γ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] (Γ ++ I ∷ []) Δ (J ⊗ J') = let⊗-Ic2-n-false Γ Δ f g
  ccut-Ic2-n-false {Γ = Γ₁} .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} {A} f (⊗c Γ .(Γ₀ ++ A ∷ Δ') {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀ ++ I ∷ []) Γ Δ' A =
    cong (⊗c Γ (Γ₀ ++ I ∷ Γ₁ ++ Δ')) (ccut-Ic2-n-false (Γ ++ J ∷ J' ∷ Γ₀)  f g refl)

  let⊗-Ic2-n-false Δ₀ Δ₁ (uf {Γ = Γ} f) g = trans (let⊗-Ic2-j Δ₀ Δ₁ f g) (cong (λ x → Ic Δ₀ (Γ ++ Δ₁) x refl) (let⊗-bool Δ₀ Δ₁ f g))
  let⊗-Ic2-n-false Δ₀ Δ₁ (⊗r f f₁) g =
    trans (cong (λ x → ccut false (Δ₀ ++ I ∷ []) f x refl) (ccut-Ic22 false Δ₀ [] f₁ g refl))
      (ccut-Ic2-n-false  Δ₀ f  (ccut false (Δ₀ ++ _ ∷ []) f₁ g refl) refl)
  let⊗-Ic2-n-false Δ₀ Δ₁ (⊗c Γ Δ f) g =
    cong (⊗c (Δ₀ ++ I ∷ Γ) (Δ ++ Δ₁)) (let⊗-Ic2-n-false Δ₀ Δ₁ f g)

  let⊗-Ic2-j Δ₀ Δ₁ {J = J} {J'} ax g
    rewrite cases++-inj₂ [] Δ₀ Δ₁ (J ⊗ J') = refl
  let⊗-Ic2-j Δ₀ Δ₁ (⊗r f f₁) g =
    trans (cong (λ x → ccut _ (Δ₀ ++ I ∷ []) f x refl) (ccut-Ic22 false Δ₀ [] f₁ g refl))
      (ccut-Ic2-j Δ₀ f  (ccut false (Δ₀ ++ _ ∷ []) f₁ g refl) refl)
  let⊗-Ic2-j Δ₀ Δ₁ (Il f) g = let⊗-Ic2-n-true Δ₀ Δ₁ f g
  let⊗-Ic2-j {Γ = Γ} Δ₀ Δ₁ (⊗l {A = A} {B} f) g
    rewrite cases++-inj₂ [] Δ₀ (Γ ++ Δ₁) (A ⊗ B) = cong (⊗c (Δ₀ ++ I ∷ []) (Γ ++ Δ₁)) (let⊗-Ic2-j Δ₀ Δ₁ f g)
  let⊗-Ic2-j Δ₀ Δ₁ {A} (⊗c Γ Δ {J} {J'} f) g
    rewrite cases++-inj₁ Δ₀ Γ (J ⊗ J' ∷ Δ ++ Δ₁) A =
    cong (⊗c (Δ₀ ++ I ∷ A ∷ Γ) (Δ ++ Δ₁)) (let⊗-Ic2-j Δ₀ Δ₁ f g)

  let⊗-Ic2-n-true Δ₀ Δ₁ (uf {Γ = Γ} f) g =
    trans (cong (λ x → Ic (Δ₀ ++ I ∷ []) (Γ ++ Δ₁) x refl) (let⊗-Ic2-j Δ₀ Δ₁ f g))
      (sym (IcIc2 Δ₀ (Γ ++ Δ₁) (let⊗ true Δ₀ Δ₁ f g) refl))
  let⊗-Ic2-n-true Δ₀ Δ₁ (⊗r f f₁) g =
    trans (cong (λ x → ccut true (Δ₀ ++ I ∷ []) f x refl) (ccut-Ic22 false Δ₀ [] f₁ g refl))
      (ccut-Ic2-n-true Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) f₁ g refl) refl)
  let⊗-Ic2-n-true Δ₀ Δ₁ (⊗c Γ Δ {J} {J'} f) g 
    rewrite cases++-inj₁ Δ₀ Γ (J ⊗ J' ∷ Δ ++ Δ₁) I =
    cong (⊗c (Δ₀ ++ I ∷ I ∷ Γ) (Δ ++ Δ₁)) (let⊗-Ic2-n-true Δ₀ Δ₁ f g)
  
  ccut-Ic2-n-true Δ₀ f ax eq =  ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic2-n-true Δ₀ f (uf g) eq with cases∷ Δ₀ eq
  ccut-Ic2-n-true .[] f (uf g) eq | inj₁ (refl , refl , refl) = refl
  ccut-Ic2-n-true .(_ ∷ Γ₀) f (uf g) eq | inj₂ (Γ₀ , refl , refl) =
    cong uf (ccut-Ic2-n-true Γ₀ f g refl)
  ccut-Ic2-n-true Δ₀ f Ir eq =  ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic2-n-true Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
  ccut-Ic2-n-true {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} {A = A} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀) Δ I | cases++-inj₁ (Δ₀ ++ I ∷ []) Γ₀ Δ A = 
    cong₂ (⊗r {Γ = Δ₀ ++ _ ∷ _ ∷ Γ ++ Γ₀} {Δ}) (ccut-Ic2-n-true Δ₀ f g refl) refl
  ccut-Ic2-n-true {Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} {A} f (⊗r {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ (Γ₁ ++ Δ') I | cases++-inj₂ (Γ₀ ++ I ∷ []) Γ Δ' A = 
    cong (⊗r g) (ccut-Ic2-n-true Γ₀ f g₁ refl)
  ccut-Ic2-n-true Δ₀ f (Il g) eq = cong Il (ccut-Ic2-n-true Δ₀ f g eq)
  ccut-Ic2-n-true Δ₀ f (⊗l g) refl = cong ⊗l (ccut-Ic2-n-true (_ ∷ Δ₀) f g refl)
  ccut-Ic2-n-true Δ₀ {Δ'} f (⊗c Γ Δ {J} {J'} g) eq with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) eq
  ccut-Ic2-n-true {Γ = Γ} Δ₀ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} {A} f (⊗c .(Δ₀ ++ A ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀) (J ⊗ J' ∷ Δ) I | cases++-inj₁  (Δ₀ ++ I ∷ []) Γ₀ (J ⊗ J' ∷ Δ) A =
    cong (⊗c (Δ₀ ++ _ ∷ _ ∷ Γ ++ Γ₀) Δ) (ccut-Ic2-n-true Δ₀ f g refl)
  ccut-Ic2-n-true .Γ {.Δ} f (⊗c Γ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] (Γ ++ I ∷ []) Δ (J ⊗ J') = let⊗-Ic2-n-true Γ Δ f g
  ccut-Ic2-n-true {Γ = Γ₁} .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} {A} f (⊗c Γ .(Γ₀ ++ A ∷ Δ') {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (Γ₁ ++ Δ') I | cases++-inj₂ (J ⊗ J' ∷ Γ₀ ++ I ∷ []) Γ Δ' A =
    cong (⊗c Γ (Γ₀ ++ _ ∷ _ ∷ Γ₁ ++ Δ')) (ccut-Ic2-n-true (Γ ++ J ∷ J' ∷ Γ₀)  f g refl)

  ccut-Ic2-j Δ₀ f ax eq =  ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic2-j Δ₀ f (uf g) eq with cases∷ Δ₀ eq
  ccut-Ic2-j .[] f (uf g) eq | inj₁ (refl , refl , refl) = refl
  ccut-Ic2-j .(_ ∷ Γ₀) f (uf g) eq | inj₂ (Γ₀ , refl , refl) =
    cong uf (ccut-Ic2-j Γ₀ f g refl)
  ccut-Ic2-j Δ₀ f Ir eq =  ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ic2-j Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
  ccut-Ic2-j {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} {A = A}{A'} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀) Δ A' | cases++-inj₁ (Δ₀ ++ I ∷ []) Γ₀ Δ A =
    cong₂ (⊗r {Γ = Δ₀ ++ _ ∷ _ ∷ Γ ++ Γ₀} {Δ}) (ccut-Ic2-j Δ₀ f g refl) refl
  ccut-Ic2-j {Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} {A}{A'} f (⊗r {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ (Γ₁ ++ Δ') A' | cases++-inj₂ (Γ₀ ++ I ∷ []) Γ Δ' A = cong (⊗r g) (ccut-Ic2-j Γ₀ f g₁ refl)
  ccut-Ic2-j Δ₀ f (Il g) eq = cong Il (ccut-Ic2-j Δ₀ f g eq)
  ccut-Ic2-j Δ₀ f (⊗l g) refl = cong ⊗l (ccut-Ic2-j (_ ∷ Δ₀) f g refl)
  ccut-Ic2-j Δ₀ {Δ'} f (⊗c Γ Δ {J} {J'} g) eq with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) eq
  ccut-Ic2-j {Γ = Γ} Δ₀ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} {A}{A'} f (⊗c .(Δ₀ ++ A ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀) (J ⊗ J' ∷ Δ) A' | cases++-inj₁  (Δ₀ ++ I ∷ []) Γ₀ (J ⊗ J' ∷ Δ) A =
    cong (⊗c (Δ₀ ++ _ ∷ _ ∷ Γ ++ Γ₀) Δ) (ccut-Ic2-j Δ₀ f g refl)
  ccut-Ic2-j .Γ {.Δ} f (⊗c Γ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] (Γ ++ I ∷ []) Δ (J ⊗ J') = let⊗-Ic2-j Γ Δ f g
  ccut-Ic2-j {Γ = Γ₁} .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} {A}{A'} f (⊗c Γ .(Γ₀ ++ A ∷ Δ') {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (Γ₁ ++ Δ') A' | cases++-inj₂ (J ⊗ J' ∷ Γ₀ ++ I ∷ []) Γ Δ' A =
    cong (⊗c Γ (Γ₀ ++ _ ∷ _ ∷ Γ₁ ++ Δ')) (ccut-Ic2-j (Γ ++ J ∷ J' ∷ Γ₀)  f g refl)

abstract
  ccut-Ir-true : {S : Stp} → {Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {C : Fma} → 
             (g : S ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ I ∷ Δ') → 
            ccut true Δ₀ Ir g eq ≗ subst-cxt eq g
  ccut-Ir-true Δ₀ ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ir-true Δ₀ (uf g) eq with cases∷ Δ₀ eq
  ccut-Ir-true .[] (uf g) refl | inj₁ (refl , refl , refl) = uf (~ Il (≡-to-≗ (Il-1-scutIr g)) ∙ IlIl-1 g)
  ccut-Ir-true .(_ ∷ Γ₀) (uf g) refl | inj₂ (Γ₀ , refl , refl) = uf (ccut-Ir-true Γ₀  g refl)
  ccut-Ir-true Δ₀ Ir eq = ⊥-elim ([]disj∷ Δ₀ eq)
  ccut-Ir-true Δ₀ {Δ'} (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
  ccut-Ir-true Δ₀ {.(Γ₀ ++ Δ)} (⊗r {Γ = .(Δ₀ ++ I ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl) =
    ⊗r (ccut-Ir-true Δ₀ g refl) refl
  ccut-Ir-true .(Γ ++ Γ₀) {Δ'} (⊗r {Γ = Γ} {.(Γ₀ ++ I ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl) =
    ⊗r refl (ccut-Ir-true Γ₀ g₁ refl)
  ccut-Ir-true Δ₀ (Il g) refl = Il (ccut-Ir-true Δ₀ g refl)
  ccut-Ir-true Δ₀ (⊗l g) refl = ⊗l (ccut-Ir-true (_ ∷ Δ₀) g refl)
  ccut-Ir-true Δ₀ {Δ'} (⊗c Γ Δ {J} {J'} g) eq with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) eq
  ccut-Ir-true Δ₀ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} (⊗c .(Δ₀ ++ I ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl) =
    ⊗c (Δ₀ ++ I ∷ Γ₀) Δ (ccut-Ir-true Δ₀ g refl)
  ccut-Ir-true .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} (⊗c Γ .(Γ₀ ++ I ∷ Δ') {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) =
    ⊗c Γ (Γ₀ ++ I ∷ Δ') (ccut-Ir-true (Γ ++ J ∷ J' ∷ Γ₀) g refl)

abstract
  ccut-Ir-Ic : {S : Stp} (Λ₁ Λ₂ : Cxt) → {Δ : Cxt} → {A C : Fma} → 
              (g : S ∣ Δ ⊢ C) (eq : Δ ≡ Λ₁ ++ A ∷ Λ₂) →  
              ccut false Λ₁ Ir (Ic Λ₁ Λ₂ g eq) refl ≡ subst-cxt eq g
  ccut-Ir-Ic Λ₁ Λ₂ ax eq = ⊥-elim ([]disj∷ Λ₁ eq)
  ccut-Ir-Ic Λ₁ Λ₂ (uf g) eq with cases∷ Λ₁ eq
  ccut-Ir-Ic .[] Λ₂ (uf g) refl | inj₁ (refl , refl , refl) = refl
  ccut-Ir-Ic .(_ ∷ Γ₀) Λ₂ (uf g) refl | inj₂ (Γ₀ , refl , refl) =
    cong uf (ccut-Ir-Ic Γ₀ Λ₂ g refl)
  ccut-Ir-Ic Λ₁ Λ₂ Ir eq = ⊥-elim ([]disj∷ Λ₁ eq)
  ccut-Ir-Ic Λ₁ Λ₂ (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Λ₁ Γ Λ₂ Δ eq
  ccut-Ir-Ic Λ₁ .(Γ₀ ++ Δ) {A = A} (⊗r {Γ = .(Λ₁ ++ A ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Λ₁ (A ∷ Γ₀) Δ I = cong₂ (⊗r {Γ = Λ₁ ++ _ ∷ Γ₀} {Δ}) (ccut-Ir-Ic Λ₁ Γ₀ g refl) refl
  ccut-Ir-Ic .(Γ ++ Γ₀) Λ₂ {A = A} (⊗r {Γ = Γ} {.(Γ₀ ++ A ∷ Λ₂)} g g₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ (A ∷ Λ₂) I = cong (⊗r g) (ccut-Ir-Ic Γ₀ Λ₂ g₁ refl)
  ccut-Ir-Ic Λ₁ Λ₂ (Il g) refl = cong Il (ccut-Ir-Ic Λ₁ Λ₂ g refl )
  ccut-Ir-Ic Λ₁ Λ₂ (⊗l g) refl = cong ⊗l (ccut-Ir-Ic (_ ∷ Λ₁) Λ₂ g refl)
  ccut-Ir-Ic Λ₁ Λ₂ (⊗c Γ Δ {J} {J'} g) eq with cases++ Λ₁ Γ Λ₂ (J ⊗ J' ∷ Δ) eq
  ccut-Ir-Ic Λ₁ .(Γ₀ ++ J ⊗ J' ∷ Δ) {A = A} (⊗c .(Λ₁ ++ A ∷ Γ₀) Δ {J} {J'} g) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Λ₁ (A ∷ Γ₀) (J ⊗ J' ∷ Δ) I = cong (⊗c (Λ₁ ++ A ∷ Γ₀) Δ) (ccut-Ir-Ic Λ₁ (Γ₀ ++ J ∷ J' ∷ Δ) g refl)
  ccut-Ir-Ic .Γ .Δ (⊗c Γ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₁ Γ [] (J ⊗ J' ∷ Δ) I = cong (⊗c Γ Δ) (ccut-Ir-Ic Γ (J' ∷ Δ) g refl)
  ccut-Ir-Ic .(Γ ++ J ⊗ J' ∷ Γ₀) Λ₂ {A = A} (⊗c Γ .(Γ₀ ++ A ∷ Λ₂) {J} {J'} g) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (A ∷ Λ₂) I = cong (⊗c Γ (Γ₀ ++ A ∷ Λ₂)) (ccut-Ir-Ic (Γ ++ J ∷ J' ∷ Γ₀) Λ₂ g refl)


abstract
  ccut-Ir-let⊗ : {T : Stp} → {Δ : Cxt} → (Λ₁ Λ₂ : Cxt) → {C  J J' : Fma} → 
              (g : nothing ∣ Δ ⊢ J ⊗ J') (h : T ∣ Λ₁ ++ J ∷ J' ∷ Λ₂ ⊢ C) → 
              ccut false Λ₁ Ir (let⊗ true Λ₁ Λ₂ g h) refl ≡ let⊗ false Λ₁ Λ₂ g h
  ccut-Ir-ccut : {T : Stp} → {Δ Γ Λ₂ : Cxt} → (Λ₁ : Cxt) → {A C : Fma} → 
              (g : nothing ∣ Γ ⊢ A) (h : T ∣ Δ ⊢ C) (eq : Δ ≡ Λ₁ ++ A ∷ Λ₂) → 
              ccut false Λ₁ Ir (ccut true Λ₁ g h eq) refl ≡ ccut false Λ₁ g h eq

  ccut-Ir-let⊗ Λ₁ Λ₂ (uf {Γ} g) h =
    trans (ccut-Ir-Ic Λ₁ (Γ ++ Λ₂) (let⊗ true Λ₁ Λ₂ g h) refl)
      (let⊗-bool Λ₁ Λ₂ g h)
  ccut-Ir-let⊗ Λ₁ Λ₂ (⊗r g g₁) h = ccut-Ir-ccut Λ₁ g (ccut false (Λ₁ ++ _ ∷ []) g₁ h refl) refl
  ccut-Ir-let⊗ Λ₁ Λ₂ (⊗c Γ Δ {J} {J'} g) h
    rewrite cases++-inj₁ Λ₁ Γ (J ⊗ J' ∷ Δ ++ Λ₂) I =
      cong (⊗c (Λ₁ ++ Γ) (Δ ++ Λ₂)) (ccut-Ir-let⊗ Λ₁ Λ₂ g h)

  ccut-Ir-ccut Λ₁ g ax eq = ⊥-elim ([]disj∷ Λ₁ eq)
  ccut-Ir-ccut Λ₁ g (uf h) eq with cases∷ Λ₁ eq
  ccut-Ir-ccut .[] g (uf h) refl | inj₁ (refl , refl , refl) = refl
  ccut-Ir-ccut .(_ ∷ Γ₀) g (uf h) refl | inj₂ (Γ₀ , refl , refl) =
    cong uf (ccut-Ir-ccut Γ₀ g h refl)
  ccut-Ir-ccut Λ₁ g Ir eq = ⊥-elim ([]disj∷ Λ₁ eq)
  ccut-Ir-ccut {Λ₂ = Λ₂} Λ₁ g (⊗r {Γ = Γ} {Δ} h h₁) eq with cases++ Λ₁ Γ Λ₂ Δ eq
  ccut-Ir-ccut {Γ = Γ} {.(Γ₀ ++ Δ)} Λ₁ g (⊗r {Γ = .(Λ₁ ++ _ ∷ Γ₀)} {Δ} h h₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Λ₁ (Γ ++ Γ₀) Δ I = cong₂ (⊗r {Γ = Λ₁ ++ Γ ++ Γ₀}{Δ}) (ccut-Ir-ccut Λ₁ g h refl) refl
  ccut-Ir-ccut {Γ = Γ₁} {Λ₂} .(Γ ++ Γ₀) g (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Λ₂)} h h₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ (Γ₁ ++ Λ₂) I = cong (⊗r h) (ccut-Ir-ccut Γ₀ g h₁ refl)
  ccut-Ir-ccut Λ₁ g (Il h) eq = cong Il (ccut-Ir-ccut Λ₁ g h eq)
  ccut-Ir-ccut Λ₁ g (⊗l h) refl = cong ⊗l (ccut-Ir-ccut (_ ∷ Λ₁) g h refl)
  ccut-Ir-ccut {Λ₂ = Λ₂} Λ₁ g (⊗c Γ Δ {J} {J'} h) eq with cases++ Λ₁ Γ Λ₂ (J ⊗ J' ∷ Δ) eq
  ccut-Ir-ccut {Γ = Γ} {.(Γ₀ ++ J ⊗ J' ∷ Δ)} Λ₁ g (⊗c .(Λ₁ ++ _ ∷ Γ₀) Δ {J} {J'} h) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Λ₁ (Γ ++ Γ₀) (J ⊗ J' ∷ Δ) I = cong (⊗c (Λ₁ ++ Γ ++ Γ₀) Δ) (ccut-Ir-ccut Λ₁ g h refl)
  ccut-Ir-ccut {Λ₂ = .Δ} .Γ g (⊗c Γ Δ {J} {J'} h) refl | inj₂ ([] , refl , refl) = ccut-Ir-let⊗ Γ Δ g h 
  ccut-Ir-ccut {Γ = Γ₁} {Λ₂} .(Γ ++ J ⊗ J' ∷ Γ₀) g (⊗c Γ .(Γ₀ ++ _ ∷ Λ₂) {J} {J'} h) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (Γ₁ ++ Λ₂) I = cong (⊗c Γ (Γ₀ ++ Γ₁ ++ Λ₂)) (ccut-Ir-ccut (Γ ++ J ∷ J' ∷ Γ₀) g h refl)

  ccut-let⊗-s-true : {b : Bool} {S₁ T : Stp} → {Γ Δ : Cxt} → (Λ₁ Λ₂ : Cxt) → {C  J J' : Fma} → 
              (f : S₁ ∣ Γ ⊢ I) (g : nothing ∣ Δ ⊢ J ⊗ J') (h : T ∣ Λ₁ ++ J ∷ J' ∷ Λ₂ ⊢ C) → 
              ccut b Λ₁ f (let⊗ true Λ₁ Λ₂ g h) refl ≗ let⊗ b Λ₁ Λ₂ (scut f (Il g)) h
  ccut-let⊗-s-true Λ₁ Λ₂ ax g h = ≡-to-≗ (ccut-ax Λ₁ (let⊗ true Λ₁ Λ₂ g h) refl)
  ccut-let⊗-s-true {false} Λ₁ Λ₂ (uf f) g h =
    ≡-to-≗ (ccut-uf Λ₁ f (let⊗ true Λ₁ Λ₂ g h) refl)
    ∙ ccut-let⊗-s-true Λ₁ Λ₂ f g h
  ccut-let⊗-s-true {true} {Δ = Δ} Λ₁ Λ₂ (uf {Γ = Γ} f) g h = 
    ≡-to-≗ (ccut-uf-true Λ₁ f (let⊗ true Λ₁ Λ₂ g h) refl)
    ∙ cong-Ic Λ₁ (Γ ++ Δ ++ Λ₂) (ccut-let⊗-s-true Λ₁ Λ₂ f g h) refl 
  ccut-let⊗-s-true {false} Λ₁ Λ₂ Ir g h = ≡-to-≗ (ccut-Ir-let⊗ Λ₁ Λ₂ g h) 
  ccut-let⊗-s-true {true} Λ₁ Λ₂ Ir g h = ccut-Ir-true Λ₁ (let⊗ true Λ₁ Λ₂ g h) refl
  ccut-let⊗-s-true Λ₁ Λ₂ (Il f) g h =
    ≡-to-≗ (ccut-Il _ Λ₁ f (let⊗ true Λ₁ Λ₂ g h) refl)
    ∙ ccut-let⊗-s-true Λ₁ Λ₂ f g h 
  ccut-let⊗-s-true {Δ = Δ} Λ₁ Λ₂ (⊗l {Γ = Γ} f) g h =
    ccut-⊗l _ Λ₁ f (let⊗ true Λ₁ Λ₂ g h) refl
    ∙ ⊗c Λ₁ (Γ ++ Δ ++ Λ₂) (ccut-let⊗-s-true Λ₁ Λ₂ f g h)
  ccut-let⊗-s-true {b}{S₁} {Δ = Δ₁} Λ₁ Λ₂ (⊗c Γ Δ f) g h =
    ccut-⊗c Λ₁ Γ Δ f (let⊗ true Λ₁ Λ₂ g h) refl
    ∙ ⊗c (Λ₁ ++ asCxt b S₁ Γ) (Δ ++ Δ₁ ++ Λ₂) (ccut-let⊗-s-true Λ₁ Λ₂ f g h)
