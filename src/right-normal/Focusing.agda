{-# OPTIONS --rewriting #-}

module Focusing where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities

open import Fsk
open import SeqCalc

-- ====================================================================

-- A focused sequent calculus

-- =====================================================================
 
-- We need to postulate function extensionality

postulate
  funext : {A B : Set} {f g : A → B}
    → (∀ x → f x ≡ g x) → f ≡ g

-- =======================================================================

-- irreducible stoup

StpR : Set
StpR = Maybe At

-- open formulae

noCl : Fma → Set
noCl A = isCl A → ⊥

data noCls : Cxt → Set where
  is-[] : noCls []
  is-∷ : {A : Fma} {Γ : Cxt}
    → noCl A → noCls Γ → noCls (A ∷ Γ)

noCl-++ : {Γ Δ : Cxt} → noCls (Γ ++ Δ) → noCls Γ × noCls Δ
noCl-++ {[]} nΔ = is-[] , nΔ
noCl-++ {A ∷ Γ}{Δ} (is-∷ nA nΓΔ) =
  is-∷ nA (noCl-++ {Γ}{Δ} nΓΔ .proj₁) , noCl-++ nΓΔ .proj₂

-- Checking whether a formula is closed is decidable

isCl? : (A : Fma) → noCl A ⊎ isCl A
isCl? (` X) = inj₁ (λ ())
isCl? I = inj₂ isI
isCl? (A ⊗ B) with isCl? A | isCl? B
isCl? (A ⊗ B) | inj₁ x | q = inj₁ (λ { (is⊗ x₁ x₂) → x x₁ })
isCl? (A ⊗ B) | inj₂ y | inj₁ x = inj₁ (λ { (is⊗ x₁ x₂) → x x₂ })
isCl? (A ⊗ B) | inj₂ y | inj₂ y₁ = inj₂ (is⊗ y y₁)

isCl-eq : {J : Fma} (cJ : isCl J) → isCl? J ≡ inj₂ cJ
isCl-eq {J} cJ with isCl? J
isCl-eq {J} cJ | inj₁ x = ⊥-elim (x cJ)
isCl-eq {J} cJ | inj₂ y = cong inj₂ (uniq-cl _ _)

-- ==========================================================

-- The focused sequent calculus

infix 15 _∣_；_⊢C_ _∣_⊢L_ _∣_⊢R_

mutual
  data _∣_；_⊢C_ : Stp → Cxt → Cxt → Fma → Set where
    act : {S : Stp} (Γ : Cxt) {Δ : Cxt} {A C : Fma}
      → (nA : noCl A) (f : S ∣ Γ ； A ∷ Δ ⊢C C)
      → S ∣ Γ ++ A ∷ [] ； Δ ⊢C C
    Ic : {S : Stp} (Γ : Cxt) (Δ : Cxt) {C : Fma}
      → (f : S ∣ Γ ； Δ ⊢C C)
      → S ∣ Γ ++ I ∷ [] ； Δ  ⊢C C 
    ⊗c : {S : Stp} (Γ : Cxt) (Δ : Cxt) {C J J' : Fma}
      → (cJ : isCl J) (cJ' : isCl J')
      → (f : S ∣ Γ ++ J ∷ J' ∷ [] ； Δ ⊢C C)
      → S ∣ Γ ++ J ⊗ J' ∷ [] ； Δ  ⊢C C 
    switch : {S : Stp} {Γ : Cxt} {C : Fma}
      → (f : S ∣ Γ ⊢L C)
      → S ∣ [] ； Γ ⊢C C
      
  data _∣_⊢L_ : Stp → Cxt → Fma → Set where
    Il : {Γ : Cxt} → {C : Fma} → 
              nothing ∣ Γ ⊢L C → just I ∣ Γ ⊢L C 
    ⊗l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ B ∷ [] ； Γ ⊢C C → just (A ⊗ B) ∣ Γ ⊢L C
    uf : {Γ : Cxt} {A C : Fma} → 
              just A ∣ Γ ⊢L C → nothing ∣ A ∷ Γ ⊢L C
    switch :  {S : StpR} {T : Stp} (nS : mmap ` S ≡ T) → 
              {Γ : Cxt} {C : Fma} → 
              (f : S ∣ Γ ⊢R C) → T ∣ Γ ⊢L C

  data _∣_⊢R_ : StpR → Cxt → Fma → Set where
    ax : {X : At} → just X ∣ [] ⊢R ` X
    Ir : nothing ∣ [] ⊢R I
    ⊗r : {S : StpR} → {Γ Δ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢R A → nothing ∣ Δ ⊢L B → S ∣ Γ ++ Δ ⊢R A ⊗ B 

-- Admissible rules in C-mode

IlC : {Γ Δ : Cxt} → {C : Fma} → 
  nothing ∣ Γ ； Δ ⊢C C → just I ∣ Γ ； Δ ⊢C C 
IlC (act _ nA f) = act _ nA (IlC f)
IlC (Ic _ _ f) = Ic _ _ (IlC f)
IlC (⊗c _ _ cJ cJ' f) = ⊗c _ _ cJ cJ' (IlC f)
IlC (switch f) = switch (Il f)


⊗lC' : {Γ Γ' Δ : Cxt} → {A B C : Fma} → 
  just A ∣ Γ' ； Δ ⊢C C → Γ' ≡ B ∷ Γ → just (A ⊗ B) ∣ Γ ； Δ ⊢C C
⊗lC' (act [] nA f) refl = switch (⊗l (act _ nA f))
⊗lC' (act (B ∷ Γ) nA f) refl = act _ nA (⊗lC' f refl)
⊗lC' (Ic [] _ f) refl = switch (⊗l (Ic _ _ f))
⊗lC' (Ic (B ∷ Γ) _ f) refl = Ic _ _ (⊗lC' f refl)
⊗lC' (⊗c [] _ cJ cJ' f) refl = switch (⊗l (⊗c [] _ cJ cJ' f))
⊗lC' (⊗c (B ∷ Γ) _ cJ cJ' f) refl = ⊗c _ _ cJ cJ' (⊗lC' f refl)

⊗lC : {Γ Δ : Cxt} → {A B C : Fma} → 
  just A ∣ B ∷ Γ ； Δ ⊢C C → just (A ⊗ B) ∣ Γ ； Δ ⊢C C
⊗lC f = ⊗lC' f refl

⊗lC'-[] : {Γ Δ : Cxt} → {A B C : Fma}
  → (f : just A ∣ Γ ； Δ ⊢C C) (eq : Γ ≡ B ∷ [])
  → ⊗lC' f eq ≡ switch (⊗l (subst (λ x → just A ∣ x ； Δ ⊢C C) eq f))
⊗lC'-[] (act [] nA f) refl = refl
⊗lC'-[] (act (_ ∷ Γ) nA f) eq = ⊥-elim ([]disj∷ Γ (sym (inj∷ eq .proj₂)))
⊗lC'-[] (Ic [] _ f) refl = refl
⊗lC'-[] (Ic (_ ∷ Γ) _ f) eq = ⊥-elim ([]disj∷ Γ (sym (inj∷ eq .proj₂)))
⊗lC'-[] (⊗c [] _ cJ cJ' f) refl = refl
⊗lC'-[] (⊗c (_ ∷ Γ) _ cJ cJ' f) eq = ⊥-elim ([]disj∷ Γ (sym (inj∷ eq .proj₂)))

⊗lC-[] : {Δ : Cxt} → {A B C : Fma}
  → (f : just A ∣ B ∷ [] ； Δ ⊢C C) 
  → ⊗lC f ≡ switch (⊗l f)
⊗lC-[] f = ⊗lC'-[]  f refl

ufC : {Γ Δ : Cxt} {A C : Fma}
  → just A ∣ Γ ； Δ ⊢C C → nothing ∣ A ∷ Γ ； Δ ⊢C C
ufC (act _ nA f) = act _ nA (ufC f)
ufC (Ic _ _ f) = Ic _ _ (ufC f)
ufC (⊗c Γ Δ cJ cJ' f) = ⊗c (_ ∷ Γ) Δ cJ cJ' (ufC f)
ufC {A = A} (switch f) with isCl? A
ufC {A = A} (switch f) | inj₁ nA = act [] nA (switch (uf f))
ufC {A = .I} (switch (Il f)) | inj₂ isI = Ic _ _ (switch f)
ufC {A = .I} (switch (switch {nothing} () f)) | inj₂ isI
ufC {A = .I} (switch (switch {just x} () f)) | inj₂ isI
ufC {A = .(_ ⊗ _)} (switch (⊗l f)) | inj₂ (is⊗ cJ cJ') = ⊗c [] _ cJ cJ' (ufC f)
ufC {A = .(_ ⊗ _)} (switch (switch {nothing} () f)) | inj₂ (is⊗ cJ cJ')
ufC {A = .(_ ⊗ _)} (switch (switch {just x} () f)) | inj₂ (is⊗ cJ cJ')

ufC-switch : {Γ : Cxt} {A C : Fma}
  → (f : just A ∣ Γ ⊢L C) (nA : noCl A)
  → ufC (switch f) ≡ act [] nA (switch (uf f))
ufC-switch {A = A} f nA with isCl? A
ufC-switch {A = A} f nA | inj₁ x = cong (λ z → act [] z (switch (uf f))) (funext (λ z → ⊥-elim (x z)))
ufC-switch {A = A} f nA | inj₂ y = ⊥-elim (nA y)

IcC' : {S : Stp} (Γ : Cxt) {Γ' Δ Λ : Cxt} {C : Fma}
  → (f : S ∣ Λ ； Δ ⊢C C) → Λ ≡ Γ ++ Γ'
  → S ∣ Γ ++ I ∷ Γ' ； Δ  ⊢C C
IcC' Γ {Γ'} (act Λ nA f) eq with cases++ Λ Γ [] Γ' (sym eq)
IcC' ._ {.[]} (act Λ {A = A} nA f) eq | inj₁ ([] , refl , refl) =
  Ic (Λ ++ A ∷ []) _ (act _ nA f)
IcC' Γ {.(Γ₀ ++ _ ∷ [])} (act .(Γ ++ Γ₀) nA f) eq | inj₂ (Γ₀ , refl , refl) =
  act (Γ ++ I ∷ Γ₀) nA (IcC' Γ f refl)
IcC' Γ {Γ'} (Ic Λ _ f) eq with cases++ Λ Γ [] Γ' (sym eq)
IcC' ._ {.[]} (Ic Λ _ f) eq | inj₁ ([] , refl , refl) =
  Ic (Λ ++ I ∷ []) _ (Ic _ _ f)
IcC' Γ {.(Γ₀ ++ I ∷ [])} (Ic .(Γ ++ Γ₀) _ f) eq | inj₂ (Γ₀ , refl , refl) =
  Ic (Γ ++ I ∷ Γ₀) _ (IcC' Γ f refl)
IcC' Γ {Γ'} (⊗c Λ _ cJ cJ' f) eq with cases++ Λ Γ [] Γ' (sym eq)
IcC' ._ {.[]} (⊗c Λ _ cJ cJ' f) eq | inj₁ ([] , refl , refl) =
  Ic (Λ ++ _ ∷ []) _ (⊗c _ _ cJ cJ' f)
IcC' Γ {.(Γ₀ ++ _ ∷ [])} (⊗c .(Γ ++ Γ₀) _ cJ cJ' f) eq | inj₂ (Γ₀ , refl , refl) =
  ⊗c (Γ ++ I ∷ Γ₀) _ cJ cJ' (IcC' Γ f refl) 
IcC' [] (switch f) refl = Ic _ _ (switch f)  

IcC : {S : Stp} (Γ : Cxt) {Γ' Δ : Cxt} {C : Fma}
  → (f : S ∣ Γ ++ Γ' ； Δ ⊢C C)
  → S ∣ Γ ++ I ∷ Γ' ； Δ  ⊢C C
IcC Γ f = IcC' Γ f refl

IcC-[] : {S : Stp} (Γ : Cxt) {Δ : Cxt} {C : Fma}
  → (f : S ∣ Γ ； Δ ⊢C C) 
  → IcC Γ {[]} f ≡ Ic Γ _ f
IcC-[] .(Γ ++ _ ∷ []) (act Γ {A = A} nA f)
  rewrite cases++-inj₁ Γ [] [] A = refl
IcC-[] .(Γ ++ I ∷ []) (Ic Γ _ f) 
  rewrite cases++-inj₁ Γ [] [] I = refl
IcC-[] .(Γ ++ _ ∷ []) (⊗c Γ _ {J = J}{J'}_ _ f) 
  rewrite cases++-inj₁ Γ [] [] (J ⊗ J') = refl
IcC-[] .[] (switch f) = refl

⊗cC' : {S : Stp} (Γ : Cxt) {Γ' Δ Λ : Cxt} {C J J' : Fma}
  → (cJ : isCl J)(cJ' : isCl J')
  → (f : S ∣ Λ ； Δ ⊢C C) → Λ ≡ Γ ++ J ∷ J' ∷ Γ' 
  → S ∣ Γ ++ J ⊗ J' ∷ Γ' ； Δ  ⊢C C
⊗cC' Γ {Γ'} cJ cJ' (act Λ nA f) eq with cases++ Λ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC' Γ {Γ'} cJ cJ' (act .(Γ ++ J ∷ Γ₀) nA f) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗cC' Γ {.[]} cJ cA (act .(Γ ++ J ∷ []) nA f) eq | inj₂ (J ∷ [] , p , refl) | refl , refl = ⊥-elim (nA cA)
⊗cC' Γ {.(Γ₀ ++ _ ∷ [])} cJ cJ' (act .(Γ ++ J ∷ J' ∷ Γ₀) nA f) eq | inj₂ (J ∷ J' ∷ Γ₀ , p , refl) | refl , refl =
  act (Γ ++ _ ∷ Γ₀) nA (⊗cC' Γ cJ cJ' f refl)
⊗cC' Γ {Γ'}  cJ cJ' (Ic Λ _ f) eq with cases++ Λ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC' Γ {Γ'} cJ cJ' (Ic .(Γ ++ J ∷ Γ₀) _ f) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗cC' Γ {.[]} cJ cJ' (Ic .(Γ ++ J ∷ []) _ f) eq | inj₂ (J ∷ [] , p , refl) | refl , refl =
  ⊗c Γ _ cJ isI (Ic (Γ ++ J ∷ []) _ f)
⊗cC' Γ {Γ'} cJ cJ' (Ic .(Γ ++ J ∷ J' ∷ Γ₀) _ f) eq | inj₂ (J ∷ J' ∷ Γ₀ , refl , refl) | refl , r =
  Ic (Γ ++ J ⊗ J' ∷ Γ₀) _ (⊗cC' Γ cJ cJ' f refl)
⊗cC' Γ {Γ'} cJ cJ' (⊗c Λ _ cK cK' f) eq with cases++ Λ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC' Γ {Γ'} cJ cJ' (⊗c .(Γ ++ J ∷ Γ₀) _ cK cK' f) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗cC' Γ {.[]} cJ cJ' (⊗c .(Γ ++ J ∷ []) _ cK cK' f) eq | inj₂ (J ∷ [] , p , refl) | refl , refl =
  ⊗c Γ _ cJ (is⊗ cK cK') (⊗c (Γ ++ J ∷ []) _ cK cK' f)
⊗cC' Γ {Γ'} cJ cJ' (⊗c .(Γ ++ J ∷ J' ∷ Γ₀) _ cK cK' f) eq | inj₂ (J ∷ J' ∷ Γ₀ , refl , refl) | refl , r =
  ⊗c (Γ ++ J ⊗ J' ∷ Γ₀) _ cK cK' (⊗cC' Γ cJ cJ' f refl)
⊗cC' Γ cJ cJ' (switch f) eq = ⊥-elim ([]disj∷ Γ eq)

⊗cC : {S : Stp} (Γ : Cxt) {Γ' Δ : Cxt} {C J J' : Fma}
  → (cJ : isCl J)(cJ' : isCl J')
  → (f : S ∣ Γ ++ J ∷ J' ∷ Γ' ； Δ ⊢C C)
  → S ∣ Γ ++ J ⊗ J' ∷ Γ' ； Δ  ⊢C C
⊗cC Γ cJ cJ' f = ⊗cC' Γ cJ cJ' f refl

⊗cC'-[] : {S : Stp} (Γ : Cxt) {Δ Γ' : Cxt} {C J J' : Fma}
  → {cJ : isCl J}{cJ' : isCl J'}
  → (f : S ∣ Γ' ； Δ ⊢C C) (eq : Γ' ≡ Γ ++ J ∷ J' ∷ [])
  → ⊗cC' Γ {[]} cJ cJ' f eq ≡ ⊗c Γ _ cJ cJ' (subst (λ x → S ∣ x ； Δ ⊢C C) eq f)
⊗cC'-[] Γ (act Γ₁ nA f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ []) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC'-[] Γ (act .(Γ ++ J ∷ Γ₀) nA f) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗cC'-[] Γ {cJ' = cJ'} (act .(Γ ++ J ∷ []) nA f) eq | inj₂ (J ∷ [] , refl , refl) | refl , refl = ⊥-elim (nA cJ') 
⊗cC'-[] Γ (act .(Γ ++ J ∷ x ∷ Γ₀) nA f) eq | inj₂ (J ∷ x ∷ Γ₀ , p , refl) | refl , r = ⊥-elim ([]disj∷ Γ₀ (inj∷ r .proj₂))
⊗cC'-[] Γ (Ic Γ₁ Δ f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ []) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC'-[] Γ (Ic .(Γ ++ J ∷ Γ₀) Δ f) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗cC'-[] Γ {cJ' = isI} (Ic .(Γ ++ J ∷ []) Δ f) refl | inj₂ (J ∷ [] , p , refl) | refl , refl = refl
⊗cC'-[] Γ (Ic .(Γ ++ J ∷ x ∷ Γ₀) Δ f) eq | inj₂ (J ∷ x ∷ Γ₀ , p , refl) | refl , r = ⊥-elim ([]disj∷ Γ₀ (inj∷ r .proj₂))
⊗cC'-[] Γ (⊗c Γ₁ Δ cJ cJ' f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ []) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC'-[] Γ (⊗c .(Γ ++ J ∷ Γ₀) Δ cJ cJ' f) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗cC'-[] Γ (⊗c .(Γ ++ J ∷ []) Δ cJ cJ' f) refl | inj₂ (J ∷ [] , p , refl) | refl , refl =
  cong (λ x → ⊗c Γ Δ _ x (⊗c (Γ ++ _ ∷ []) Δ cJ cJ' f)) (uniq-cl _ _)
⊗cC'-[] Γ (⊗c .(Γ ++ J ∷ x ∷ Γ₀) Δ cJ cJ' f) eq | inj₂ (J ∷ x ∷ Γ₀ , p , refl) | refl , r = ⊥-elim ([]disj∷ Γ₀ (inj∷ r .proj₂))
⊗cC'-[] Γ (switch f) eq =  ⊥-elim ([]disj∷ Γ eq) 

mutual
  ⊗rCL : {S : Stp} → {Γ Δ Λ : Cxt} → {A B : Fma}
    → S ∣ Γ ； Δ ⊢C A → nothing ∣ Λ ⊢L B
    → S ∣ Γ ； Δ ++ Λ ⊢C A ⊗ B
  ⊗rCL (act _ nA f) g = act _ nA (⊗rCL f g)
  ⊗rCL (Ic _ _ f) g = Ic _ _ (⊗rCL f g)
  ⊗rCL (⊗c _ _ cJ cJ' f) g = ⊗c _ _ cJ cJ' (⊗rCL f g)
  ⊗rCL (switch f) g = switch (⊗rLL f g)

  ⊗rLL : {S : Stp} → {Γ Δ : Cxt} → {A B : Fma}
    → S ∣ Γ ⊢L A → nothing ∣ Δ ⊢L B
    → S ∣ Γ ++ Δ ⊢L A ⊗ B
  ⊗rLL (Il f) g = Il (⊗rLL f g)
  ⊗rLL (⊗l f) g = ⊗l (⊗rCL f g)
  ⊗rLL (uf f) g = uf (⊗rLL f g)
  ⊗rLL (switch nS f) g = switch nS (⊗r f g) 

⊗rC : {S : Stp} → {Γ Δ Λ : Cxt} → {A B : Fma}
  → S ∣ Γ ； [] ⊢C A → nothing ∣ Δ ； Λ ⊢C B
  → S ∣ Γ ++ Δ ； Λ ⊢C A ⊗ B
⊗rC {Γ = Γ} f (act Γ' nA g) = act (Γ ++ Γ') nA (⊗rC f g)
⊗rC {Γ = Γ} f (Ic Γ' _ g) = Ic (Γ ++ Γ') _ (⊗rC f g)
⊗rC {Γ = Γ} f (⊗c Γ' _ cJ cJ' g) = ⊗c (Γ ++ Γ') _ cJ cJ' (⊗rC f g)
⊗rC f (switch g) = ⊗rCL f g  

axC : {A : Fma} → just A ∣ [] ； [] ⊢C A
axC {` X} = switch (switch refl ax)
axC {I} = switch (Il (switch refl Ir))
axC {A ⊗ B} = ⊗lC (⊗rC axC (ufC axC))

-- =======================================================================

-- Embedding of focused derivation into the unfocused calculus

mutual 
  embC : {S : Stp} → {Γ Δ : Cxt} → {C : Fma} →
              S ∣ Γ ； Δ ⊢C C → S ∣ Γ ++ Δ ⊢ C
  embC (act _ nA f) = embC f
  embC (Ic Γ _ f) = Ic Γ _ (embC f)
  embC (⊗c Γ _ cJ cJ' f) = ⊗c Γ _ cJ cJ' (embC f)
  embC (switch f) = embL f

  embL : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢L C → S ∣ Γ ⊢ C
  embL (Il f) = Il (embL f)
  embL (⊗l f) = ⊗l (embC f)
  embL (uf f) = uf (embL f)
  embL (switch refl f) = embR f

  embR : {S : StpR} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢R C → mmap ` S ∣ Γ ⊢ C
  embR ax = ax
  embR Ir = Ir
  embR (⊗r f₁ f₂) = ⊗r (embR f₁) (embL f₂)

emb : {S : Stp} → {Γ : Cxt} → {C : Fma}
  → S ∣ Γ ； [] ⊢C C → S ∣ Γ ⊢ C
emb = embC

-- the focusing function 

focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢ C → S ∣ Γ ； [] ⊢C C
focus ax = axC
focus (uf f) = ufC (focus f) 
focus Ir = switch (switch refl Ir)
focus (⊗r f g) = ⊗rC (focus f) (focus g)
focus (Il f) = IlC (focus f)
focus (⊗l f) = ⊗lC (focus f)
focus (Ic Γ Δ f) = IcC Γ (focus f)
focus (⊗c Γ Δ cJ cJ' f) = ⊗cC Γ cJ cJ' (focus f)

-- A more general act rule, moving multiple formulae out of the
-- anteroom in one single go.

act⋆ : {S : Stp} (Γ : Cxt) {Δ Δ' : Cxt} {C : Fma}
  → (nΔ : noCls Δ)
  → (f : S ∣ Γ ； Δ ++ Δ' ⊢C C)
  → S ∣ Γ ++ Δ ； Δ' ⊢C C
act⋆ Γ is-[] f = f
act⋆ Γ {Δ' = Δ'} (is-∷ {A} nA nΔ) f =
  act⋆ (Γ ++ A ∷ []) nΔ (act Γ nA f)

-- Interaction of act⋆ with other admissible rules

act⋆act⋆ : {S : Stp} (Γ : Cxt) {Δ Δ' Δ'' : Cxt} {C : Fma}
  → (nΔΔ' : noCls (Δ ++ Δ'))
  → (f : S ∣ Γ ； Δ ++ Δ' ++ Δ'' ⊢C C)
  → act⋆ (Γ ++ Δ){Δ'} (noCl-++ nΔΔ' .proj₂)
       (act⋆ Γ {Δ} (noCl-++ {Δ}{Δ'} nΔΔ' .proj₁) f)
    ≡ act⋆ Γ {Δ = Δ ++ Δ'}{Δ''} nΔΔ' f
act⋆act⋆ Γ {[]} nΔ f = refl
act⋆act⋆ Γ {A ∷ Δ} (is-∷ nA nΔΔ') f =
  act⋆act⋆ (Γ ++ A ∷ []) {Δ} nΔΔ' (act Γ nA f)

act⋆-IcC : {S : Stp} {Γ Γ' Δ' Δ : Cxt} {C : Fma}
  → (nΔ : noCls Δ) (f : S ∣ Γ ++ Γ' ； Δ ++ Δ' ⊢C C)
  → IcC Γ {Γ' ++ Δ}{Δ'} (act⋆ (Γ ++ Γ') nΔ f)
     ≡ act⋆ (Γ ++ I ∷ Γ') nΔ (IcC Γ f)
act⋆-IcC is-[] f = refl
act⋆-IcC {Γ = Γ} {Γ'} (is-∷ {A} nA nΔ) f = 
  trans (act⋆-IcC {Γ = Γ}{Γ' ++ _ ∷ []} nΔ (act (Γ ++ Γ') nA f))
    lem
  where
    lem : act⋆ (Γ ++ I ∷ Γ' ++ _ ∷ []) nΔ (IcC Γ (act (Γ ++ Γ') nA f))
          ≡ act⋆ (Γ ++ I ∷ Γ' ++ _ ∷ []) nΔ (act (Γ ++ I ∷ Γ') nA (IcC Γ f))
    lem rewrite cases++-inj₂ Γ' Γ [] A = refl

act⋆-⊗cC : {S : Stp} {Γ Γ' Δ' Δ : Cxt} {C J J' : Fma}
  → {cJ : isCl J}{cJ' : isCl J'}
  → (nΔ : noCls Δ) (f : S ∣ Γ ++ J ∷ J' ∷ Γ' ； Δ ++ Δ' ⊢C C)
  → ⊗cC Γ {Γ' ++ Δ}{Δ'} cJ cJ' (act⋆ (Γ ++ _ ∷ _ ∷ Γ') nΔ f)
     ≡ act⋆ (Γ ++ _ ∷ Γ') nΔ (⊗cC Γ cJ cJ' f)
act⋆-⊗cC is-[] f = refl
act⋆-⊗cC {Γ = Γ} {Γ'} {J = J}{J'} (is-∷ {A} nA nΔ) f = 
  trans (act⋆-⊗cC {Γ = Γ}{Γ' ++ _ ∷ []} nΔ (act (Γ ++ _ ∷ _ ∷ Γ') nA f))
    lem
  where
    lem : act⋆ (Γ ++ _ ∷ Γ' ++ _ ∷ []) nΔ (⊗cC Γ _ _ (act (Γ ++ _ ∷ _ ∷ Γ') nA f))
          ≡ act⋆ (Γ ++ _ ∷ Γ' ++ _ ∷ []) nΔ (act (Γ ++ _ ∷ Γ') nA (⊗cC Γ _ _ f))
    lem rewrite cases++-inj₂ (J ∷ J' ∷ Γ') Γ [] A = refl

act⋆-IlC : {Γ Δ' Δ : Cxt} {C : Fma}
  → (nΔ : noCls Δ) (f : nothing ∣ Γ ； Δ ++ Δ' ⊢C C)
  → IlC {Γ ++ Δ}{Δ'} (act⋆ Γ nΔ f) ≡ act⋆ Γ nΔ (IlC f)
act⋆-IlC is-[] f = refl
act⋆-IlC {Γ} (is-∷ {A} nA nΔ) f =
  act⋆-IlC {Γ ++ A ∷ []} nΔ (act Γ nA f)  

act⋆-⊗lC : {Γ Δ' Δ : Cxt} {A B C : Fma}
  → (nΔ : noCls Δ) (f : just A ∣ B ∷ Γ ； Δ ++ Δ' ⊢C C)
  → ⊗lC (act⋆ (B ∷ Γ) {_}{Δ'} nΔ f)
     ≡ act⋆ Γ nΔ (⊗lC f)
act⋆-⊗lC is-[] f = refl
act⋆-⊗lC {Γ} (is-∷ {A} nA nΔ) f =
  act⋆-⊗lC {Γ ++ A ∷ []} nΔ (act (_ ∷ Γ) nA f)  

act⋆-ufC : {Γ Δ' Δ : Cxt} {A C : Fma}
  → (nΔ : noCls Δ) (f : just A ∣ Γ ； Δ ++ Δ' ⊢C C)
  → ufC {Γ ++ Δ}{Δ'} (act⋆ Γ nΔ f) ≡ act⋆ (A ∷ Γ) nΔ (ufC f)
act⋆-ufC is-[] f = refl
act⋆-ufC {Γ} (is-∷ {A} nA nΔ) f =
  act⋆-ufC {Γ ++ A ∷ []} nΔ (act Γ nA f)  


act-⊗rCL : {S : Stp} → {Γ Δ Δ' Λ : Cxt} → {A B : Fma}
  → (f : S ∣ Γ ； Δ ++ Δ' ⊢C A) (g : nothing ∣ Λ ⊢L B)
  → (nΔ : noCls Δ)
  → ⊗rCL (act⋆ Γ {Δ' = Δ'} nΔ f) g ≡ act⋆ Γ nΔ (⊗rCL f g)
act-⊗rCL f g is-[] = refl
act-⊗rCL {Γ = Γ} f g (is-∷ {A} nA nΔ) =
  act-⊗rCL {Γ = Γ ++ A ∷ []} (act Γ nA f) g nΔ

act-⊗rC : {S : Stp} → {Γ Δ Λ Λ' : Cxt} → {A B : Fma}
  → (f : S ∣ Γ ； [] ⊢C A) (g : nothing ∣ Δ ； Λ ++ Λ' ⊢C B)
  → (nΛ : noCls Λ)
  → ⊗rC {Λ = Λ'} f (act⋆ Δ nΛ g) ≡ act⋆ (Γ ++ Δ) nΛ (⊗rC f g)
act-⊗rC f g is-[] = refl
act-⊗rC {Γ = Γ} {Δ} f g (is-∷ {A} nA nΛ) =
  act-⊗rC {Γ = Γ}{Δ ++ A ∷ []} f (act Δ nA g) nΛ

-- focus ∘ emb ≡ id

mutual 
  focus-embC : {S : Stp} → {Γ Δ : Cxt} → {C : Fma}
    → (nΔ : noCls Δ) (f : S ∣ Γ ； Δ ⊢C C)
    → focus (embC f) ≡ act⋆ Γ nΔ f
  focus-embC nΔ (act Γ nA f) = focus-embC (is-∷ nA nΔ) f
  focus-embC nΔ (Ic Γ _ f) =
    trans (cong (λ x → IcC' Γ x refl) (focus-embC nΔ f))
      (trans (act⋆-IcC nΔ f)
        (cong (act⋆ (Γ ++ I ∷ []) nΔ) (IcC-[] Γ f))) 
  focus-embC nΔ (⊗c Γ _ cJ cJ' f) =
    trans (cong (λ x → ⊗cC' Γ cJ cJ' x refl) (focus-embC nΔ f))
      (trans (act⋆-⊗cC nΔ f)
        (cong (act⋆ (Γ ++ _ ∷ []) nΔ) (⊗cC'-[] Γ f refl)))
  focus-embC nΔ (switch f) = focus-embL nΔ f

  focus-embL : {S : Stp} → {Γ : Cxt} → {C : Fma}
    → (nΓ : noCls Γ) (f : S ∣ Γ ⊢L C)
    → focus (embL f) ≡ act⋆ [] nΓ (switch f)
  focus-embL nΓ (Il f) =
    trans (cong IlC (focus-embL nΓ f))
      (act⋆-IlC nΓ (switch f))
  focus-embL nΓ (⊗l f) =
    trans (cong ⊗lC (focus-embC nΓ f))
      (trans (act⋆-⊗lC nΓ f)
        (cong (act⋆ [] nΓ) (⊗lC-[] f)))
  focus-embL (is-∷ nA nΓ) (uf f) = 
    trans (cong ufC (focus-embL nΓ f))
      (trans (act⋆-ufC nΓ (switch f))
        (cong (act⋆ (_ ∷ []) nΓ) (ufC-switch f nA)))
  focus-embL nΓ (switch refl f) = focus-embR f nΓ

  focus-embR : {S : StpR} → {Γ : Cxt} → {C : Fma}
    → (f : S ∣ Γ ⊢R C) (nΓ : noCls Γ)
    → focus (embR f) ≡ act⋆ [] nΓ (switch (switch refl f))
  focus-embR ax is-[] = refl
  focus-embR Ir is-[] = refl
  focus-embR (⊗r {Γ = Γ} {Δ} f g) nΓΔ =
    trans (cong₂ ⊗rC (focus-embR f (noCl-++ {Γ}{Δ} nΓΔ .proj₁))
                     (focus-embL (noCl-++ {Γ}{Δ} nΓΔ .proj₂) g))
      (trans (act-⊗rC (act⋆ []
                            (noCl-++ {Γ}{Δ} nΓΔ .proj₁)
                            (switch (switch refl f)))
                      (switch g)
                      (noCl-++ {Γ}{Δ} nΓΔ .proj₂))
        (trans (cong (act⋆ Γ (noCl-++ {Γ}{Δ} nΓΔ .proj₂))
                     (act-⊗rCL (switch (switch refl f))
                               g
                               (noCl-++ {Γ}{Δ} nΓΔ .proj₁)))
          (act⋆act⋆ [] {Γ} nΓΔ (switch (switch refl (⊗r f g))))))

focus-emb : {S : Stp} → {Γ : Cxt} → {C : Fma}
  → (f : S ∣ Γ ； [] ⊢C C)
  → focus (emb f) ≡ f
focus-emb f = focus-embC is-[] f  



-- focus is compatible with ≗
-- This requires us to prove several equations in the focused calculus


⊗rCLufC : {Γ Δ Λ : Cxt}{A A' B : Fma}
  → (f : just A' ∣ Γ ； Δ ⊢C A)(g : nothing ∣ Λ ⊢L B)
  → ⊗rCL (ufC f) g ≡ ufC (⊗rCL f g)
⊗rCLufC {A' = A'} (act Γ nA f) g =
  cong (act (A' ∷ Γ) nA) (⊗rCLufC f g)
⊗rCLufC {A' = A'} (Ic Γ _ f) g =
  cong (Ic (A' ∷ Γ) _) (⊗rCLufC f g)
⊗rCLufC {A' = A'} (⊗c Γ _ _ _ f) g =
  cong (⊗c (A' ∷ Γ) _ _ _) (⊗rCLufC f g)
⊗rCLufC {A' = A'} (switch f) g with isCl? A'
⊗rCLufC {A' = A'} (switch f) g | inj₁ x = refl
⊗rCLufC {A' = .I} (switch (Il f)) g | inj₂ isI = refl
⊗rCLufC {A' = .I} (switch (switch {nothing} () f)) g | inj₂ isI
⊗rCLufC {A' = .I} (switch (switch {just x} () f)) g | inj₂ isI
⊗rCLufC {A' = .(_ ⊗ _)} (switch (⊗l x)) g | inj₂ (is⊗ y y₁) =
  cong (⊗c [] _ y y₁) (⊗rCLufC x g)
⊗rCLufC {A' = .(_ ⊗ _)} (switch (switch {nothing} () f)) g | inj₂ (is⊗ y y₁)
⊗rCLufC {A' = .(_ ⊗ _)} (switch (switch {just x} () f)) g | inj₂ (is⊗ y y₁)


⊗rCufC : {Γ Δ Λ : Cxt}{A A' B : Fma}
  → (f : just A' ∣ Γ ； [] ⊢C A)(g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (ufC f) g ≡ ufC (⊗rC f g)
⊗rCufC {Γ₁} {A' = A'} f (act Γ nA g) =
  cong (act (A' ∷ Γ₁ ++ Γ) nA) (⊗rCufC f g)
⊗rCufC {Γ₁} {A' = A'} f (Ic Γ _ g) =
  cong (Ic (A' ∷ Γ₁ ++ Γ) _) (⊗rCufC f g)
⊗rCufC {Γ₁} {A' = A'} f (⊗c Γ _ _ _ g) =
  cong (⊗c (A' ∷ Γ₁ ++ Γ) _ _ _) (⊗rCufC f g)
⊗rCufC f (switch g) = ⊗rCLufC f g

⊗rCLIlC : {Γ Δ Λ : Cxt}{A B : Fma}
  → (f : nothing ∣ Γ ； Δ ⊢C A)(g : nothing ∣ Λ ⊢L B)
  → ⊗rCL (IlC f) g ≡ IlC (⊗rCL f g)
⊗rCLIlC (act Γ nA f) g = cong (act Γ nA) (⊗rCLIlC f g)
⊗rCLIlC (Ic Γ _ f) g = cong (Ic Γ _) (⊗rCLIlC f g)
⊗rCLIlC (⊗c Γ _ _ _ f) g = cong (⊗c Γ _ _ _) (⊗rCLIlC f g)
⊗rCLIlC (switch f) g = refl

⊗rCIlC : {Γ Δ Λ : Cxt}{A B : Fma}
  → (f : nothing ∣ Γ ； [] ⊢C A)(g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (IlC f) g ≡ IlC (⊗rC f g)
⊗rCIlC {Γ₁} f (act Γ nA g) = cong (act (Γ₁ ++ Γ) nA) (⊗rCIlC f g)
⊗rCIlC {Γ₁} f (Ic Γ _ g) = cong (Ic (Γ₁ ++ Γ) _) (⊗rCIlC f g)
⊗rCIlC {Γ₁} f (⊗c Γ _ _ _ g) = cong (⊗c (Γ₁ ++ Γ) _ _ _) (⊗rCIlC f g)
⊗rCIlC f (switch g) = ⊗rCLIlC f g

⊗rCL⊗lC : {Γ Γ' Δ Λ : Cxt}{A A' B B' : Fma}
  → (f : just A' ∣ Γ' ； Δ ⊢C A)(g : nothing ∣ Λ ⊢L B)
  → (eq : Γ' ≡ B' ∷ Γ)
  → ⊗rCL (⊗lC' f eq) g ≡ ⊗lC' (⊗rCL f g) eq
⊗rCL⊗lC (act [] nA f) g refl = refl
⊗rCL⊗lC (act (B ∷ Γ) nA f) g refl = cong (act Γ nA) (⊗rCL⊗lC f g refl)
⊗rCL⊗lC (Ic [] _ f) g refl = refl
⊗rCL⊗lC (Ic (B ∷ Γ) _ f) g refl = cong (Ic Γ _) (⊗rCL⊗lC f g refl)
⊗rCL⊗lC (⊗c [] _ _ _ f) g refl = refl
⊗rCL⊗lC (⊗c (B ∷ Γ) _ _ _ f) g refl = cong (⊗c Γ _ _ _) (⊗rCL⊗lC f g refl)

⊗rC⊗lC : {Γ Δ Λ : Cxt}{A A' B B' : Fma}
  → (f : just A' ∣ B' ∷ Γ ； [] ⊢C A)(g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (⊗lC f) g ≡ ⊗lC (⊗rC f g)
⊗rC⊗lC {Γ₁} f (act Γ nA g) = cong (act (Γ₁ ++ Γ) nA) (⊗rC⊗lC f g)
⊗rC⊗lC {Γ₁} f (Ic Γ _ g) = cong (Ic (Γ₁ ++ Γ) _) (⊗rC⊗lC f g)
⊗rC⊗lC {Γ₁} f (⊗c Γ _ _ _ g) = cong (⊗c (Γ₁ ++ Γ) _ _ _) (⊗rC⊗lC f g)
⊗rC⊗lC f (switch g) = ⊗rCL⊗lC f g refl

⊗rCLIcC1 : {S : Stp}{Γ Γ' Γ'' Δ Λ : Cxt}{A B : Fma}
  → (f : S ∣ Γ'' ； Δ ⊢C A) (g : nothing ∣ Λ ⊢L B)
  → (eq : Γ'' ≡ Γ ++ Γ')
  → ⊗rCL (IcC' Γ {Γ'} f eq) g ≡ IcC' Γ (⊗rCL f g) eq
⊗rCLIcC1 {Γ = Γ₁} {Γ'} (act Γ nA f) g eq with cases++ Γ Γ₁ [] Γ' (sym eq)
⊗rCLIcC1 (act Γ nA f) g eq | inj₁ ([] , refl , refl) = refl
⊗rCLIcC1 {Γ = Γ₁} (act _ nA f) g eq | inj₂ (Γ₀ , refl , refl) =
  cong (act (Γ₁ ++ I ∷ Γ₀) nA) (⊗rCLIcC1 f g refl)
⊗rCLIcC1 {Γ = Γ₁} {Γ'} (Ic Γ _ f) g eq with cases++ Γ Γ₁ [] Γ' (sym eq)
⊗rCLIcC1 (Ic Γ _ f) g eq | inj₁ ([] , refl , refl) = refl
⊗rCLIcC1 (Ic Γ _ f) g eq | inj₁ (x ∷ Γ₀ , refl , ())
⊗rCLIcC1 {Γ = Γ₁} (Ic ._ _ f) g eq | inj₂ (Γ₀ , refl , refl) =
  cong (Ic (Γ₁ ++ I ∷ Γ₀) _) (⊗rCLIcC1 f g refl)
⊗rCLIcC1 {Γ = Γ₁} {Γ'} (⊗c Γ _ _ _ f) g eq with cases++ Γ Γ₁ [] Γ' (sym eq)
⊗rCLIcC1 (⊗c Γ _ _ _ f) g eq | inj₁ ([] , refl , refl) = refl
⊗rCLIcC1 (⊗c Γ _ _ _ f) g eq | inj₁ (x ∷ Γ₀ , refl , ())
⊗rCLIcC1 {Γ = Γ₁} (⊗c ._ _ _ _ f) g eq | inj₂ (Γ₀ , refl , refl) =
  cong (⊗c (Γ₁ ++ I ∷ Γ₀) _ _ _) (⊗rCLIcC1 f g refl)
⊗rCLIcC1 {Γ = []} (switch f) g refl = refl

⊗rCIcC1 : {S : Stp}{Γ Γ' Δ Λ : Cxt}{A B : Fma}
  → (f : S ∣ Γ ++ Γ' ； [] ⊢C A) (g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (IcC Γ {Γ'} f) g ≡ IcC Γ (⊗rC f g)
⊗rCIcC1 {Γ = Γ₁} {Γ'} f (act Γ {A = A} nA g)
  rewrite cases++-inj₂ (Γ' ++ Γ) Γ₁ [] A =
    cong (act (Γ₁ ++ I ∷ Γ' ++ Γ) nA) (⊗rCIcC1 f g)
⊗rCIcC1 {Γ = Γ₁} {Γ'} f (Ic Γ _ g) 
  rewrite cases++-inj₂ (Γ' ++ Γ) Γ₁ [] I =
    cong (Ic (Γ₁ ++ I ∷ Γ' ++ Γ) _) (⊗rCIcC1 f g)
⊗rCIcC1 {Γ = Γ₁} {Γ'} f (⊗c Γ _ {J = J}{J'} _ _ g) 
  rewrite cases++-inj₂ (Γ' ++ Γ) Γ₁ [] (J ⊗ J') =
    cong (⊗c (Γ₁ ++ _ ∷ Γ' ++ Γ) _ _ _) (⊗rCIcC1 f g)
⊗rCIcC1 f (switch g) = ⊗rCLIcC1 f g refl

⊗rCIcC'2 : {S : Stp}{Γ Δ Δ' Δ'' Λ : Cxt}{A B : Fma}
  → (f : S ∣ Γ ； [] ⊢C A) (g : nothing ∣ Δ'' ； Λ ⊢C B)
  → (eq : Δ'' ≡ Δ ++ Δ')
  → ⊗rC f (IcC' Δ {Δ'} g eq) ≡ IcC' (Γ ++ Δ) (⊗rC f g) (cong (Γ ++_) eq)
⊗rCIcC'2 {Δ = Δ} {Δ'} f (act Γ nA g) eq with cases++ Γ Δ [] Δ' (sym eq)
⊗rCIcC'2 {Γ = Γ₁} {.(Γ ++ A ∷ [])} {.[]} f (act Γ {A = A} nA g) refl | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Γ) [] [] A = refl
⊗rCIcC'2 {Γ = Γ} {Δ} {.(Γ₀ ++ A ∷ [])} f (act .(Δ ++ Γ₀) {A = A} nA g) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ (Γ ++ Δ) [] A =
    cong (act (Γ ++ Δ ++ I ∷ Γ₀) nA) (⊗rCIcC'2 f g refl)
⊗rCIcC'2 {Δ = Δ} {Δ'} f (Ic Γ _ g) eq with cases++ Γ Δ [] Δ' (sym eq)
⊗rCIcC'2 {Γ = Γ₁} {.(Γ ++ I ∷ [])} {.[]} f (Ic Γ _ g) refl | inj₁ ([] , refl , refl) 
  rewrite cases++-inj₁ (Γ₁ ++ Γ) [] [] I = refl
⊗rCIcC'2 {Γ = Γ} {Δ} {.(Γ₀ ++ I ∷ [])} f (Ic .(Δ ++ Γ₀) _ g) refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ (Γ ++ Δ) [] I =
    cong (Ic (Γ ++ Δ ++ I ∷ Γ₀) _) (⊗rCIcC'2 f g refl)
⊗rCIcC'2 {Δ = Δ} {Δ'} f (⊗c Γ _ _ _ g) eq with cases++ Γ Δ [] Δ' (sym eq)
⊗rCIcC'2 {Γ = Γ₁} {.(Γ ++ _ ∷ [])} {.[]} f (⊗c Γ _ {J = J}{J'} _ _ g) refl | inj₁ ([] , refl , refl) 
  rewrite cases++-inj₁ (Γ₁ ++ Γ) [] [] (J ⊗ J') = refl
⊗rCIcC'2 {Γ = Γ} {Δ} {.(Γ₀ ++ _ ∷ [])} f (⊗c .(Δ ++ Γ₀) _ {J = J}{J'} _ _ g) refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ (Γ ++ Δ) [] (J ⊗ J') =
    cong (⊗c (Γ ++ Δ ++ _ ∷ Γ₀) _ _ _) (⊗rCIcC'2 f g refl)
⊗rCIcC'2 {Γ = Γ} {[]} f (switch g) refl = sym (IcC-[] Γ (⊗rCL f g))

⊗rCIcC2 : {S : Stp}{Γ Δ Δ' Λ : Cxt}{A B : Fma}
  → (f : S ∣ Γ ； [] ⊢C A) (g : nothing ∣ Δ ++ Δ' ； Λ ⊢C B)
  → ⊗rC f (IcC Δ {Δ'} g) ≡ IcC (Γ ++ Δ) (⊗rC f g)
⊗rCIcC2 f g = ⊗rCIcC'2 f g refl

⊗rCL⊗cC1 : {S : Stp}{Γ Γ' Γ'' Δ Λ : Cxt}{A B J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : S ∣ Γ'' ； Δ ⊢C A) (g : nothing ∣ Λ ⊢L B)
  → (eq : Γ'' ≡ Γ ++ J ∷ J' ∷ Γ')
  → ⊗rCL (⊗cC' Γ {Γ'} cJ cJ' f eq) g ≡ ⊗cC' Γ cJ cJ' (⊗rCL f g) eq
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (act Γ nA f) g eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (act .(Γ₁ ++ x ∷ Γ₀) nA f) g eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗rCL⊗cC1 {Γ = Γ₁} {.[]} {cJ' = cJ'} (act .(Γ₁ ++ x ∷ []) nA f) g refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = ⊥-elim (nA cJ')
⊗rCL⊗cC1 {Γ = Γ₁} {.(Γ₀ ++ _ ∷ [])} (act .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) nA f) g refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (act (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) nA) (⊗rCL⊗cC1 f g refl)
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (Ic Γ Δ f) g eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (Ic .(Γ₁ ++ x ∷ Γ₀) Δ f) g eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗rCL⊗cC1 {Γ = Γ₁} {.[]} (Ic .(Γ₁ ++ x ∷ []) Δ f) g refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = refl
⊗rCL⊗cC1 {Γ = Γ₁} {.(Γ₀ ++ I ∷ [])} (Ic .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ f) g refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (Ic (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) _) (⊗rCL⊗cC1 f g refl)
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (⊗c Γ Δ _ _ f) g eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (⊗c .(Γ₁ ++ x ∷ Γ₀) Δ _ _ f) g eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗rCL⊗cC1 {Γ = Γ₁} {.[]} (⊗c .(Γ₁ ++ x ∷ []) Δ _ _ f) g refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = refl
⊗rCL⊗cC1 {Γ = Γ₁} {.(Γ₀ ++ _ ∷ [])} (⊗c .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ _ _ f) g refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (⊗c (Γ₁ ++ _ ⊗ _ ∷ Γ₀) _ _ _) (⊗rCL⊗cC1 f g refl)
⊗rCL⊗cC1 {Γ = Γ} (switch f) g eq = ⊥-elim ([]disj∷ Γ eq)


⊗rC⊗cC1 : {S : Stp}{Γ Γ' Δ Λ : Cxt}{A B J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : S ∣ Γ ++ J ∷ J' ∷ Γ' ； [] ⊢C A) (g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (⊗cC Γ {Γ'} cJ cJ' f) g ≡ ⊗cC Γ cJ cJ' (⊗rC f g)
⊗rC⊗cC1 {Γ = Γ₁} {Γ'} {J = J} {J'} f (act Γ {A = A} nA g)
  rewrite cases++-inj₂ (J ∷ J' ∷ Γ' ++ Γ) Γ₁ [] A =
  cong (act (Γ₁ ++ J ⊗ J' ∷ Γ' ++ Γ) nA) (⊗rC⊗cC1 f g)
⊗rC⊗cC1 {Γ = Γ₁} {Γ'} {J = J} {J'} f (Ic Γ Δ g)
  rewrite cases++-inj₂ (J ∷ J' ∷ Γ' ++ Γ) Γ₁ [] I =
  cong (Ic (Γ₁ ++ J ⊗ J' ∷ Γ' ++ Γ) _) (⊗rC⊗cC1 f g)
⊗rC⊗cC1 {Γ = Γ₁} {Γ'} {J = J} {J'} f (⊗c Γ Δ {J = K} {K'} _ _ g) 
  rewrite cases++-inj₂ (J ∷ J' ∷ Γ' ++ Γ) Γ₁ [] (K ⊗ K') =
  cong (⊗c (Γ₁ ++ J ⊗ J' ∷ Γ' ++ Γ) _ _ _) (⊗rC⊗cC1 f g)
⊗rC⊗cC1 f (switch f₁) = ⊗rCL⊗cC1 f f₁ refl

⊗rC⊗cC'2 : {S : Stp}{Γ Δ Δ' Δ'' Λ : Cxt}{A B J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : S ∣ Γ ； [] ⊢C A) (g : nothing ∣ Δ'' ； Λ ⊢C B)
  → (eq : Δ'' ≡ Δ ++ J ∷ J' ∷ Δ')
  → ⊗rC f (⊗cC' Δ {Δ'} cJ cJ' g eq) ≡ ⊗cC' (Γ ++ Δ) cJ cJ' (⊗rC f g) (cong (Γ ++_) eq)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ} {Δ'} f (act Γ nA g) eq with cases++ Γ Δ [] (_ ∷ _ ∷ Δ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ} {Δ'} f (act .(Δ ++ x ∷ Γ₀) nA g) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗rC⊗cC'2 {Γ = Γ₁} {Δ} {.[]} {cJ' = cJ'} f (act .(Δ ++ x ∷ []) nA g) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = ⊥-elim (nA cJ')
⊗rC⊗cC'2 {Γ = Γ₁} {Δ} {.(Γ₀ ++ A ∷ [])} f (act .(Δ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA g) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ Δ) [] A = 
  cong (act (Γ₁ ++ Δ ++ x ⊗ x₁ ∷ Γ₀) nA) (⊗rC⊗cC'2 f g refl)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {Δ'} {A = A} f (Ic Γ Δ g) eq with cases++ Γ Δ₁ [] (_ ∷ _ ∷ Δ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {Δ'} {A = A} f (Ic .(Δ₁ ++ J ∷ Γ₀) Δ g) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {.[]} {A = A} f (Ic .(Δ₁ ++ J ∷ []) Δ g) refl | inj₂ (J ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (J ∷ []) (Γ₁ ++ Δ₁) [] I = refl
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {.(Γ₀ ++ I ∷ [])} {A = A} f (Ic .(Δ₁ ++ J ∷ x ∷ Γ₀) Δ g) refl | inj₂ (J ∷ x ∷ Γ₀ , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (J ∷ x ∷ Γ₀) (Γ₁ ++ Δ₁) [] I =
  cong (Ic (Γ₁ ++ Δ₁ ++ J ⊗ x ∷ Γ₀) Δ) (⊗rC⊗cC'2 f g refl)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {Δ'} {A = A} f (⊗c Γ Δ cK cK' g) eq with cases++ Γ Δ₁ [] (_ ∷ _ ∷ Δ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {Δ'} {A = A} f (⊗c .(Δ₁ ++ J ∷ Γ₀) Δ cK cK' g) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {.[]} {A = A} f (⊗c .(Δ₁ ++ J ∷ []) Δ {J = K}{K'} cK cK' g) refl | inj₂ (J ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (J ∷ []) (Γ₁ ++ Δ₁) [] (K ⊗ K') = refl
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {.(Γ₀ ++ _ ∷ [])} {A = A} f (⊗c .(Δ₁ ++ J ∷ x ∷ Γ₀) Δ {J = K}{K'} _ _ g) refl | inj₂ (J ∷ x ∷ Γ₀ , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (J ∷ x ∷ Γ₀) (Γ₁ ++ Δ₁) [] (K ⊗ K') =
  cong (⊗c (Γ₁ ++ Δ₁ ++ J ⊗ x ∷ Γ₀) Δ _ _) (⊗rC⊗cC'2 f g refl)
⊗rC⊗cC'2 {Δ = Δ} f (switch f₁) eq = ⊥-elim ([]disj∷ Δ eq)

⊗rC⊗cC2 : {S : Stp}{Γ Δ Δ' Λ : Cxt}{A B J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : S ∣ Γ ； [] ⊢C A) (g : nothing ∣ Δ ++ J ∷ J' ∷ Δ' ； Λ ⊢C B)
  → ⊗rC f (⊗cC Δ {Δ'} cJ cJ' g) ≡ ⊗cC (Γ ++ Δ) cJ cJ' (⊗rC f g)
⊗rC⊗cC2 f g = ⊗rC⊗cC'2 f g refl

IlCIcC' : {Γ Γ' Δ Λ : Cxt} {C : Fma}
  → (f : nothing ∣ Γ' ； Λ ⊢C C)
  → (eq : Γ' ≡ Γ ++ Δ)
  → IlC (IcC' Γ {Δ} f eq) ≡ IcC' Γ (IlC f) eq
IlCIcC' {Γ₁} {Δ = Δ} (act Γ nA f) eq with cases++ Γ Γ₁ [] Δ (sym eq)
IlCIcC' {.(Γ ++ _ ∷ [])} {Δ = .[]} (act Γ nA f) eq | inj₁ ([] , refl , refl) = refl
IlCIcC' {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (act .(Γ₁ ++ Γ₀) nA f) eq | inj₂ (Γ₀ , refl , refl) =
  cong (act (Γ₁ ++ I ∷ Γ₀) nA) (IlCIcC' f refl)
IlCIcC' {Γ₁} {Δ = Δ} (Ic Γ _ f) eq with cases++ Γ Γ₁ [] Δ (sym eq)
IlCIcC' {.(Γ ++ I ∷ [])} {Δ = .[]} (Ic Γ _ f) eq | inj₁ ([] , refl , refl) = refl
IlCIcC' {Γ₁} {Δ = .(Γ₀ ++ I ∷ [])} (Ic .(Γ₁ ++ Γ₀) _ f) eq | inj₂ (Γ₀ , refl , refl) =
  cong (Ic (Γ₁ ++ I ∷ Γ₀) _) (IlCIcC' f refl)
IlCIcC' {Γ₁} {Δ = Δ} (⊗c Γ _ _ _ f) eq with cases++ Γ Γ₁ [] Δ (sym eq)
IlCIcC' {.(Γ ++ _ ∷ [])} {Δ = .[]} (⊗c Γ _ _ _ f) eq | inj₁ ([] , refl , refl) = refl
IlCIcC' {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (⊗c .(Γ₁ ++ Γ₀) _ _ _ f) eq | inj₂ (Γ₀ , refl , refl) =
  cong (⊗c (Γ₁ ++ _ ∷ Γ₀) _ _ _) (IlCIcC' f refl)
IlCIcC' {[]} (switch f) refl = refl

IlCIcC : {Γ Δ Λ : Cxt} {C : Fma}
  → (f : nothing ∣ Γ ++ Δ ； Λ ⊢C C)
  → IlC (IcC Γ {Δ} f) ≡ IcC Γ (IlC f)
IlCIcC f = IlCIcC' f refl

IlC⊗cC' : {Γ Γ' Δ Λ : Cxt} {C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : nothing ∣ Γ' ； Λ ⊢C C)
  → (eq : Γ' ≡ Γ ++ J ∷ J' ∷ Δ)
  → IlC (⊗cC' Γ {Δ} cJ cJ' f eq) ≡ ⊗cC' Γ cJ cJ' (IlC f) eq
IlC⊗cC' {Γ₁} {Δ = Δ} (act Γ nA f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
IlC⊗cC' {Γ₁} {Δ = Δ} (act .(Γ₁ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
IlC⊗cC' {Γ₁} {Δ = .[]} {cJ' = cJ'} (act .(Γ₁ ++ x ∷ []) nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = ⊥-elim (nA cJ')
IlC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (act .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (act (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) nA) (IlC⊗cC' f refl)
IlC⊗cC' {Γ₁} {Δ = Δ₁} (Ic Γ Δ f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
IlC⊗cC' {Γ₁} {Δ = Δ₁} (Ic .(Γ₁ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
IlC⊗cC' {Γ₁} {Δ = .[]} (Ic .(Γ₁ ++ x ∷ []) Δ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = refl
IlC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ I ∷ [])} (Ic .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (Ic (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) _) (IlC⊗cC' f refl)
IlC⊗cC' {Γ₁} {Δ = Δ₁} (⊗c Γ Δ _ _ f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
IlC⊗cC' {Γ₁} {Δ = Δ₁} (⊗c .(Γ₁ ++ x ∷ Γ₀) Δ _ _ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
IlC⊗cC' {Γ₁} {Δ = .[]} (⊗c .(Γ₁ ++ x ∷ []) Δ _ _ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = refl
IlC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (⊗c .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ _ _ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (⊗c (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) _ _ _) (IlC⊗cC' f refl)
IlC⊗cC' {Γ} (switch f) eq = ⊥-elim ([]disj∷ Γ eq)

IlC⊗cC : {Γ Δ Λ : Cxt} {C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : nothing ∣ Γ ++ J ∷ J' ∷ Δ ； Λ ⊢C C)
  → IlC (⊗cC Γ {Δ} cJ cJ' f) ≡ ⊗cC Γ cJ cJ' (IlC f)
IlC⊗cC f = IlC⊗cC' f refl

⊗lCIcC' : {Γ Γ' Δ Λ : Cxt} {A B C : Fma}
    → (f : just A ∣ Γ' ； Λ ⊢C C)
    → (eq : Γ' ≡ B ∷ Γ ++ Δ)
    → ⊗lC' (IcC' (B ∷ Γ) {Δ} f eq) refl ≡ IcC' Γ (⊗lC' f eq) refl
⊗lCIcC' {Γ₁} {Δ = Δ} {B = B} (act Γ nA f) eq with cases++ Γ (B ∷ Γ₁) [] Δ (sym eq)
⊗lCIcC' {.[]} {Δ = .[]} {B = _} (act [] nA f) refl | inj₁ ([] , refl , refl) = refl
⊗lCIcC' {.(Γ ++ A ∷ [])} {Δ = .[]} {B = .x} (act (x ∷ Γ) {A = A} nA f) refl | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Γ [] [] A = refl    
⊗lCIcC' {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} {B = B} (act .(B ∷ Γ₁ ++ Γ₀) {A = A} nA f) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Γ₁ [] A =
    cong (act (Γ₁ ++ I ∷ Γ₀) nA) (⊗lCIcC' f refl)
⊗lCIcC' {Γ₁} {Δ = Δ} {B = B} (Ic Γ _ f) eq with cases++ Γ (B ∷ Γ₁) [] Δ (sym eq)
⊗lCIcC' {.[]} {Δ = .[]} {B = .I} (Ic [] _ f) refl | inj₁ ([] , refl , refl) = refl
⊗lCIcC' {.(Γ ++ I ∷ [])} {Δ = .[]} {B = .x} (Ic (x ∷ Γ) _ f) refl | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Γ [] [] I = refl    
⊗lCIcC' {Γ₁} {Δ = .(Γ₀ ++ I ∷ [])} {B = B} (Ic .(B ∷ Γ₁ ++ Γ₀) _ f) refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ Γ₁ [] I =
    cong (Ic (Γ₁ ++ I ∷ Γ₀) _) (⊗lCIcC' f refl)
⊗lCIcC' {Γ₁} {Δ = Δ} {B = B} (⊗c Γ _ _ _ f) eq with cases++ Γ (B ∷ Γ₁) [] Δ (sym eq)
⊗lCIcC' {.[]} {Δ = .[]} {B = .(_ ⊗ _)} (⊗c [] _ _ _ f) refl | inj₁ ([] , refl , refl) = refl
⊗lCIcC' {.(Γ ++ _ ⊗ _ ∷ [])} {Δ = .[]} {B = .x} (⊗c (x ∷ Γ) _ {J = J}{J'} _ _ f) refl | inj₁ ([] , refl , refl) 
  rewrite cases++-inj₁ Γ [] [] (J ⊗ J') = refl
⊗lCIcC' {Γ₁} {Δ = .(Γ₀ ++ _ ⊗ _ ∷ [])} {B = B} (⊗c .(B ∷ Γ₁ ++ Γ₀) _ {J = J}{J'} _ _ f) refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ Γ₁ [] (J ⊗ J') =
    cong (⊗c (Γ₁ ++ _ ∷ Γ₀) _ _ _) (⊗lCIcC' f refl)

⊗lCIcC : {Γ Δ Λ : Cxt} {A B C : Fma}
    → (f : just A ∣ B ∷ Γ ++ Δ ； Λ ⊢C C)
    → ⊗lC (IcC (B ∷ Γ) {Δ} f) ≡ IcC Γ (⊗lC f)
⊗lCIcC f = ⊗lCIcC' f refl

⊗lC⊗cC' : {Γ Γ' Δ Λ : Cxt} {A B C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
    → (f : just A ∣ Γ' ； Λ ⊢C C)
    → (eq : Γ' ≡ B ∷ Γ ++ J ∷ J' ∷ Δ)
    → ⊗lC' (⊗cC' (B ∷ Γ) {Δ} cJ cJ' f eq) refl ≡ ⊗cC' Γ cJ cJ' (⊗lC' f eq) refl
⊗lC⊗cC' {Γ₁} {Δ = Δ} (act Γ nA f) eq with cases++ Γ (_ ∷ Γ₁) [] (_ ∷ _ ∷ Δ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗lC⊗cC' {Γ₁} {Δ = Δ} (act .(_ ∷ Γ₁ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗lC⊗cC' {Γ₁} {Δ = .[]} {cJ' = cJ'} (act .(_ ∷ Γ₁ ++ x ∷ []) {A = A} nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = ⊥-elim (nA cJ')
⊗lC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ A ∷ [])} (act .(_ ∷ Γ₁ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] A =
    cong (act (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) nA) (⊗lC⊗cC' f refl)
⊗lC⊗cC' {Γ₁} {Δ = Δ₁} (Ic Γ Δ f) eq with cases++ Γ (_ ∷ Γ₁) [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗lC⊗cC' {Γ₁} {Δ = Δ₁} (Ic .(_ ∷ Γ₁ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗lC⊗cC' {Γ₁} {Δ = .[]} (Ic .(_ ∷ Γ₁ ++ x ∷ []) Δ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ []) Γ₁ [] I = refl
⊗lC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ I ∷ [])} (Ic .(_ ∷ Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] I =
  cong (Ic (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ) (⊗lC⊗cC' f refl)
⊗lC⊗cC' {Γ₁} {Δ = Δ₁} (⊗c Γ Δ _ _ f) eq with cases++ Γ (_ ∷ Γ₁) [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗lC⊗cC' {Γ₁} {Δ = Δ₁} (⊗c .(_ ∷ Γ₁ ++ x ∷ Γ₀) Δ _ _ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗lC⊗cC' {Γ₁} {Δ = .[]} (⊗c .(_ ∷ Γ₁ ++ x ∷ []) Δ {J = J}{J'}_ _ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ []) Γ₁ [] (J ⊗ J') = refl
⊗lC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (⊗c .(_ ∷ Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ {J = J}{J'} _ _ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') =
  cong (⊗c (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ _ _) (⊗lC⊗cC' f refl)


⊗lC⊗cC : {Γ Δ Λ : Cxt} {A B C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
    → (f : just A ∣ B ∷ Γ ++ J ∷ J' ∷ Δ ； Λ ⊢C C)
    → ⊗lC (⊗cC (B ∷ Γ) {Δ} cJ cJ' f) ≡ ⊗cC Γ cJ cJ' (⊗lC f)
⊗lC⊗cC f = ⊗lC⊗cC' f refl

IcCIcC' : {S : Stp} {Γ Γ' Δ Λ Π : Cxt} {C : Fma}
    → (f : S ∣ Γ' ； Π ⊢C C)
    → (eq : Γ' ≡ Γ ++ Δ ++ Λ)
    → IcC' Γ {Δ ++ I ∷ Λ} (IcC' (Γ ++ Δ) {Λ} f eq) refl
          ≡ IcC' (Γ ++ I ∷ Δ) (IcC' Γ {Δ ++ Λ} f eq) refl
IcCIcC' {Γ = Γ₁} {Δ = Δ} {Λ} (act Γ nA f) eq with cases++ Γ (Γ₁ ++ Δ) [] Λ (sym eq) | cases++ Γ Γ₁ [] (Δ ++ Λ) (sym eq)
IcCIcC' (act Γ {A = A} nA f) eq | inj₁ ([] , refl , refl) | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ (Γ ++ A ∷ []) [] [] I | cases++-inj₂ [] (Γ ++ A ∷ []) [] I | cases++-inj₁ Γ [] [] A = refl
IcCIcC' {Γ = Γ₁} (act .(Γ₁ ++ Γ₀) {A = A} nA f) eq | inj₁ ([] , refl , refl) | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (Γ₀ ++ A ∷ []) Γ₁ [] I | cases++-inj₂ Γ₀ Γ₁ [] A | cases++-inj₁ (Γ₁ ++ I ∷ Γ₀) [] [] A = refl
IcCIcC' {Γ = Γ₁} {Δ = Δ} (act ._ {A = A} nA f) eq | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) =  ⊥-elim ([]disj∷ (Γ₀' ++ Δ ++ Γ₀) q)
IcCIcC' {Γ = Γ₁} {Δ = Δ} (act ._ {A = A} nA f) eq | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) with ++canc {xs = Δ ++ Γ₀} {Γ₀'} Γ₁ q
IcCIcC' {Γ = Γ₁} {Δ = Δ} (act ._ {A = A} nA f) eq | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl
  rewrite cases++-inj₂ (Δ ++ I ∷ Γ₀) Γ₁ [] A | cases++-inj₂ Γ₀ (Γ₁ ++ I ∷ Δ) [] A =
    cong (act (Γ₁ ++ I ∷ Δ ++ I ∷ Γ₀) nA) (IcCIcC' f refl)
IcCIcC' {Γ = Γ₁} {Δ = Δ} {Λ} (Ic Γ _ f) eq with cases++ Γ (Γ₁ ++ Δ) [] Λ (sym eq) | cases++ Γ Γ₁ [] (Δ ++ Λ) (sym eq)
IcCIcC' (Ic Γ _ f) eq | inj₁ ([] , refl , refl) | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ (Γ ++ I ∷ []) [] [] I | cases++-inj₂ [] (Γ ++ I ∷ []) [] I | cases++-inj₁ Γ [] [] I = refl
IcCIcC' {Γ = Γ₁} (Ic _ _ f) eq | inj₁ ([] , refl , refl) | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (Γ₀ ++ I ∷ []) Γ₁ [] I | cases++-inj₂ Γ₀ Γ₁ [] I | cases++-inj₁ (Γ₁ ++ I ∷ Γ₀) [] [] I = refl
IcCIcC' {Γ = Γ₁} {Δ = Δ} (Ic _ _ f) eq | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) =  ⊥-elim ([]disj∷ (Γ₀' ++ Δ ++ Γ₀) q)
IcCIcC' {Γ = Γ₁} {Δ = Δ} (Ic _ _ f) eq | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) with ++canc {xs = Δ ++ Γ₀} {Γ₀'} Γ₁ q
IcCIcC' {Γ = Γ₁} {Δ = Δ} (Ic _ _ f) eq | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl
  rewrite cases++-inj₂ (Δ ++ I ∷ Γ₀) Γ₁ [] I | cases++-inj₂ Γ₀ (Γ₁ ++ I ∷ Δ) [] I =
    cong (Ic (Γ₁ ++ I ∷ Δ ++ I ∷ Γ₀) _) (IcCIcC' f refl)
IcCIcC' {Γ = Γ₁} {Δ = Δ} {Λ} (⊗c Γ _ _ _ f) eq with cases++ Γ (Γ₁ ++ Δ) [] Λ (sym eq) | cases++ Γ Γ₁ [] (Δ ++ Λ) (sym eq)
IcCIcC' (⊗c Γ _ {J = J}{J'} _ _ f) eq | inj₁ ([] , refl , refl) | inj₁ ([] , refl , refl) 
  rewrite cases++-inj₁ (Γ ++ (J ⊗ J') ∷ []) [] [] I | cases++-inj₂ [] (Γ ++ (J ⊗ J') ∷ []) [] I | cases++-inj₁ Γ [] [] (J ⊗ J') = refl
IcCIcC' {Γ = Γ₁} (⊗c _ _ {J = J}{J'} _ _ f) eq | inj₁ ([] , refl , refl) | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ (Γ₀ ++ J ⊗ J' ∷ []) Γ₁ [] I | cases++-inj₂ Γ₀ Γ₁ [] (J ⊗ J') | cases++-inj₁ (Γ₁ ++ I ∷ Γ₀) [] [] (J ⊗ J') = refl
IcCIcC' {Γ = Γ₁} {Δ = Δ} (⊗c _ _ {J = J}{J'} _ _ f) eq | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) =  ⊥-elim ([]disj∷ (Γ₀' ++ Δ ++ Γ₀) q)
IcCIcC' {Γ = Γ₁} {Δ = Δ} (⊗c _ _ {J = J}{J'} _ _ f) eq | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) with ++canc {xs = Δ ++ Γ₀} {Γ₀'} Γ₁ q
IcCIcC' {Γ = Γ₁} {Δ = Δ} (⊗c _ _ {J = J}{J'} _ _ f) eq | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl 
 rewrite cases++-inj₂ (Δ ++ I ∷ Γ₀) Γ₁ [] (J ⊗ J') | cases++-inj₂ Γ₀ (Γ₁ ++ I ∷ Δ) [] (J ⊗ J') =
   cong (⊗c (Γ₁ ++ _ ∷ Δ ++ _ ∷ Γ₀) _ _ _) (IcCIcC' f refl)
IcCIcC' {Γ = []} {Δ = []} {[]} (switch f) refl = refl

IcCIcC : {S : Stp} {Γ Δ Λ Π : Cxt} {C : Fma}
    → (f : S ∣ Γ ++ Δ ++ Λ ； Π ⊢C C)
    → IcC Γ {Δ ++ I ∷ Λ} (IcC (Γ ++ Δ) {Λ} f)
          ≡ IcC (Γ ++ I ∷ Δ) (IcC Γ {Δ ++ Λ} f)
IcCIcC f = IcCIcC' f refl

⊗cCIcC' : {S : Stp} {Γ Γ' Δ Λ Π : Cxt} {C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
    → (f : S ∣ Γ' ； Π ⊢C C)
    → (eq : Γ' ≡ Γ ++ J ∷ J' ∷ Δ ++ Λ)
    → ⊗cC' Γ {Δ ++ _ ∷ Λ} cJ cJ' (IcC' (Γ ++ _ ∷ _ ∷ Δ) {Λ} f eq) refl
          ≡ IcC' (Γ ++ _ ∷ Δ) (⊗cC' Γ {Δ ++ Λ} cJ cJ' f eq) refl
⊗cCIcC' {Γ = Γ₁} {Δ = Δ} {Λ} (act Γ nA f) eq with cases++ Γ (Γ₁ ++ _ ∷ _ ∷ Δ) [] Λ (sym eq)
⊗cCIcC' {Γ = Γ₁} {Δ = Δ} {.[]} (act Γ nA f) eq | inj₁ ([] , p , refl) with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ) (sym eq)
... | inj₁ (Γ₀ , p' , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cCIcC' {Γ = Γ₁} {Δ = Δ} {.[]} (act .(Γ₁ ++ x ∷ Γ₀) nA f) eq | inj₁ ([] , p , refl) | inj₂ (x ∷ Γ₀ , p' , refl) with inj∷ p'
⊗cCIcC' {Γ = Γ₁} {Δ = .[]} {.[]} {cJ' = cJ'} (act .(Γ₁ ++ x ∷ []) {A = A} nA f) refl | inj₁ ([] , refl , refl) | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ A ∷ []) Γ₁ [] I | cases++-inj₂ (x ∷ []) Γ₁ [] A = ⊥-elim (nA cJ')
⊗cCIcC' {Γ = Γ₁} {Δ = .(Γ₀ ++ A ∷ [])} {.[]} (act .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA f) refl | inj₁ ([] , refl , refl) | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀ ++ A ∷ []) Γ₁ [] I | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] A | cases++-inj₁ (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) [] [] A = refl
⊗cCIcC' {Γ = Γ₁} {Δ = Δ} {.(Γ₀ ++ A ∷ [])} {J = J} {J'} (act .(Γ₁ ++ J ∷ J' ∷ Δ ++ Γ₀) {A = A} nA f) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (J ∷ J' ∷ Δ ++ I ∷ Γ₀) Γ₁ [] A | cases++-inj₂ (J ∷ J' ∷ Δ ++ Γ₀) Γ₁ [] A | cases++-inj₂ Γ₀ (Γ₁ ++ J ∷ J' ∷ Δ) [] A | cases++-inj₂ Γ₀ (Γ₁ ++ J ⊗ J' ∷ Δ) [] A =
  cong (act (Γ₁ ++ J ⊗ J' ∷ Δ ++ I ∷ Γ₀) nA) (⊗cCIcC' f refl)
⊗cCIcC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (Ic Γ Δ f) eq with cases++ Γ (Γ₁ ++ _ ∷ _ ∷ Δ₁) [] Λ (sym eq)
⊗cCIcC' {Γ = Γ₁} {Δ = Δ₁} {.[]} (Ic Γ Δ f) eq | inj₁ ([] , p , refl) with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p' , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cCIcC' {Γ = Γ₁} {Δ = Δ₁} {.[]} (Ic .(Γ₁ ++ x ∷ Γ₀) Δ f) eq | inj₁ ([] , p , refl) | inj₂ (x ∷ Γ₀ , p' , refl) with inj∷ p'
⊗cCIcC' {Γ = Γ₁} {Δ = .[]} {.[]} (Ic .(Γ₁ ++ x ∷ []) Δ f) refl | inj₁ ([] , refl , refl) | inj₂ (x ∷ [] , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (x ∷ I ∷ []) Γ₁ [] I | cases++-inj₂ (x ∷ []) Γ₁ [] I | cases++-inj₁ Γ₁ [] []  (x ⊗ I) = refl
⊗cCIcC' {Γ = Γ₁} {Δ = .(Γ₀ ++ I ∷ [])} {.[]} (Ic .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ f) refl | inj₁ ([] , refl , refl) | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀ ++ I ∷ []) Γ₁ [] I | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] I | cases++-inj₁ (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) [] [] I = refl
⊗cCIcC' {Γ = Γ₁} {Δ = Δ₁} {.(Γ₀ ++ I ∷ [])} {J = J}{J'} (Ic .(Γ₁ ++ _ ∷ _ ∷ Δ₁ ++ Γ₀) Δ f) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (J ∷ J' ∷ Δ₁ ++ I ∷ Γ₀) Γ₁ [] I | cases++-inj₂ (J ∷ J' ∷ Δ₁ ++ Γ₀) Γ₁ [] I | cases++-inj₂ Γ₀ (Γ₁ ++ J ⊗ J' ∷ Δ₁) [] I =
  cong (Ic (Γ₁ ++ J ⊗ J' ∷ Δ₁ ++ I ∷ Γ₀) Δ) (⊗cCIcC' f refl)
⊗cCIcC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (⊗c Γ Δ _ _ f) eq with cases++ Γ (Γ₁ ++ _ ∷ _ ∷ Δ₁) [] Λ (sym eq)
⊗cCIcC' {Γ = Γ₁} {Δ = Δ₁} {.[]} (⊗c Γ Δ _ _ f) eq | inj₁ ([] , p , refl) with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p' , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cCIcC' {Γ = Γ₁} {Δ = Δ₁} {.[]} (⊗c .(Γ₁ ++ x ∷ Γ₀) Δ _ _ f) eq | inj₁ ([] , p , refl) | inj₂ (x ∷ Γ₀ , p' , refl) with inj∷ p'
⊗cCIcC' {Γ = Γ₁} {Δ = .[]} {.[]} (⊗c .(Γ₁ ++ x ∷ []) Δ {J = K}{K'}_ _ f) refl | inj₁ ([] , refl , refl) | inj₂ (x ∷ [] , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (x ∷ K ⊗ K' ∷ []) Γ₁ [] I | cases++-inj₁ Γ₁ [] [] (x ⊗ (K ⊗ K')) | cases++-inj₂ (x ∷ []) Γ₁ [] (K ⊗ K') = refl
⊗cCIcC' {Γ = Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} {.[]} (⊗c .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ {J = K}{K'}_ _ f) refl | inj₁ ([] , refl , refl) | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀ ++ K ⊗ K' ∷ []) Γ₁ [] I | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] (K ⊗ K') | cases++-inj₁ (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) [] [] (K ⊗ K') = refl
⊗cCIcC' {Γ = Γ₁} {Δ = Δ₁} {.(Γ₀ ++ _ ∷ [])} {J = J}{J'} (⊗c .(Γ₁ ++ _ ∷ _ ∷ Δ₁ ++ Γ₀) Δ {J = K}{K'} _ _ f) refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ (J ∷ J' ∷ Δ₁ ++ I ∷ Γ₀) Γ₁ [] (K ⊗ K') | cases++-inj₂ (J ∷ J' ∷ Δ₁ ++ Γ₀) Γ₁ [] (K ⊗ K') | cases++-inj₂ Γ₀ (Γ₁ ++ J ⊗ J' ∷ Δ₁) [] (K ⊗ K') =
  cong (⊗c (Γ₁ ++ J ⊗ J' ∷ Δ₁ ++ I ∷ Γ₀) Δ _ _) (⊗cCIcC' f refl)
⊗cCIcC' {Γ = Γ} (switch f) eq = ⊥-elim ([]disj∷ Γ eq)

⊗cCIcC : {S : Stp} {Γ Δ Λ Π : Cxt} {C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
    → (f : S ∣ Γ ++ J ∷ J' ∷ Δ ++ Λ ； Π ⊢C C)
    → ⊗cC Γ {Δ ++ _ ∷ Λ} cJ cJ' (IcC (Γ ++ _ ∷ _ ∷ Δ) {Λ} f)
          ≡ IcC (Γ ++ _ ∷ Δ) (⊗cC Γ {Δ ++ Λ} cJ cJ' f)
⊗cCIcC f = ⊗cCIcC' f refl

IcC⊗cC' : {S : Stp} {Γ Γ' Δ Λ Π : Cxt} {C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
    → (f : S ∣ Γ' ； Π ⊢C C)
    → (eq : Γ' ≡ Γ ++ Δ ++ J ∷ J' ∷ Λ)
    → IcC' Γ {Δ ++ _ ∷ Λ} (⊗cC' (Γ ++ Δ) {Λ} cJ cJ' f eq) refl
          ≡ ⊗cC' (Γ ++ I ∷ Δ) cJ cJ' (IcC' Γ {Δ ++ _ ∷ _ ∷ Λ} f eq) refl
IcC⊗cC' {Γ = Γ₁} {Δ = Δ} {Λ} (act Γ nA f) eq with cases++ Γ (Γ₁ ++ Δ) [] (_ ∷ _ ∷ Λ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
IcC⊗cC' {Γ = Γ₁} {Δ = Δ} {Λ} (act .(Γ₁ ++ Δ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
IcC⊗cC' {Γ = Γ₁} {Δ = Δ} {.[]} {cJ' = cJ'} (act .(Γ₁ ++ Δ ++ x ∷ []) nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = ⊥-elim (nA cJ')
IcC⊗cC' {Γ = Γ₁} {Δ = Δ} {.(Γ₀ ++ A ∷ [])} (act .(Γ₁ ++ Δ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (Δ ++ x ⊗ x₁ ∷ Γ₀) Γ₁ [] A | cases++-inj₂ (Δ ++ x ∷ x₁ ∷ Γ₀) Γ₁ [] A | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ I ∷ Δ) [] A =
  cong (act (Γ₁ ++ I ∷ Δ ++ x ⊗ x₁ ∷ Γ₀) nA) (IcC⊗cC' f refl)
IcC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (Ic Γ Δ f) eq with cases++ Γ (Γ₁ ++ Δ₁) [] (_ ∷ _ ∷ Λ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
IcC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (Ic .(Γ₁ ++ Δ₁ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
IcC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.[]} (Ic .(Γ₁ ++ Δ₁ ++ x ∷ []) Δ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ Δ₁ Γ₁ [] (x ⊗ I) | cases++-inj₂ (Δ₁ ++ x ∷ []) Γ₁ [] I | cases++-inj₂ (x ∷ []) (Γ₁ ++ I ∷ Δ₁) [] I = refl
IcC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.(Γ₀ ++ I ∷ [])} (Ic .(Γ₁ ++ Δ₁ ++ x ∷ x₁ ∷ Γ₀) Δ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Γ₁ [] I | cases++-inj₂ (Δ₁ ++ x ∷ x₁ ∷ Γ₀) Γ₁ [] I | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ I ∷ Δ₁) [] I =
  cong (Ic (Γ₁ ++ I ∷ Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ) (IcC⊗cC' f refl)
IcC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (⊗c Γ Δ _ _ f) eq with cases++ Γ (Γ₁ ++ Δ₁) [] (_ ∷ _ ∷ Λ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
IcC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (⊗c .(Γ₁ ++ Δ₁ ++ x ∷ Γ₀) Δ _ _ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
IcC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.[]} (⊗c .(Γ₁ ++ Δ₁ ++ x ∷ []) Δ {J = J}{J'} _ _ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ Δ₁ Γ₁ [] (x ⊗ (J ⊗ J')) | cases++-inj₂ (Δ₁ ++ x ∷ []) Γ₁ [] (J ⊗ J') | cases++-inj₂ (x ∷ []) (Γ₁ ++ I ∷ Δ₁) [] (J ⊗ J') = refl
IcC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.(Γ₀ ++ _ ∷ [])} (⊗c .(Γ₁ ++ Δ₁ ++ x ∷ x₁ ∷ Γ₀) Δ {J = J}{J'} _ _ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') | cases++-inj₂ (Δ₁ ++ x ∷ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ I ∷ Δ₁) [] (J ⊗ J') = 
  cong (⊗c (Γ₁ ++ _ ∷ Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ _ _) (IcC⊗cC' f refl)
IcC⊗cC' {Γ = Γ} {Δ = Δ} (switch f) eq = ⊥-elim ([]disj∷ (Γ ++ Δ) eq)

IcC⊗cC : {S : Stp} {Γ Δ Λ Π : Cxt} {C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
    → (f : S ∣ Γ ++ Δ ++ J ∷ J' ∷ Λ ； Π ⊢C C)
    → IcC Γ {Δ ++ _ ∷ Λ} (⊗cC (Γ ++ Δ) {Λ} cJ cJ' f)
          ≡ ⊗cC (Γ ++ I ∷ Δ) cJ cJ' (IcC Γ {Δ ++ _ ∷ _ ∷ Λ} f)
IcC⊗cC f = IcC⊗cC' f refl


⊗cC⊗cC' : {S : Stp} {Γ Γ' Δ Λ Π : Cxt} {C J J' K K' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → {cK : isCl K} {cK' : isCl K'}
    → (f : S ∣ Γ' ； Π ⊢C C)
    → (eq : Γ' ≡ Γ ++ K ∷ K' ∷ Δ ++ J ∷ J' ∷ Λ)
    → ⊗cC' Γ {Δ ++ _ ∷ Λ} cK cK' (⊗cC' (Γ ++ K ∷ K' ∷ Δ) {Λ} cJ cJ' f eq) refl
          ≡ ⊗cC' (Γ ++ _ ∷ Δ) cJ cJ' (⊗cC' Γ {Δ ++ _ ∷ _ ∷ Λ} cK cK' f eq) refl
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ} {Λ} (act Γ nA f) eq with cases++ Γ (Γ₁ ++ _ ∷ _ ∷ Δ) [] (_ ∷ _ ∷ Λ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ} {Λ} (act .(Γ₁ ++ _ ∷ _ ∷ Δ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ} {.[]} {cJ' = cJ'} (act .(Γ₁ ++ _ ∷ _ ∷ Δ ++ x ∷ []) nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = ⊥-elim (nA cJ')
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ} {.(Γ₀ ++ A ∷ [])} {K = K} {K'} (act .(Γ₁ ++ K ∷ K' ∷ Δ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (K ∷ K' ∷ Δ ++ x ⊗ x₁ ∷ Γ₀) Γ₁ [] A | cases++-inj₂ (K ∷ K' ∷ Δ ++ x ∷ x₁ ∷ Γ₀) Γ₁ [] A | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ K ⊗ K' ∷ Δ) [] A =
  cong (act (Γ₁ ++ K ⊗ K' ∷ Δ ++ x ⊗ x₁ ∷ Γ₀) nA) (⊗cC⊗cC' f refl)
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (Ic Γ Δ f) eq with cases++ Γ (Γ₁ ++ _ ∷ _ ∷ Δ₁) [] (_ ∷ _ ∷ Λ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (Ic .(Γ₁ ++ _ ∷ _ ∷ Δ₁ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.[]} {K = K} {K'} (Ic .(Γ₁ ++ K ∷ K' ∷ Δ₁ ++ x ∷ []) Δ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (K ∷ K' ∷ Δ₁) Γ₁ [] (x ⊗ I) | cases++-inj₂ (K ∷ K' ∷ Δ₁ ++ x ∷ []) Γ₁ [] I | cases++-inj₂ (x ∷ []) (Γ₁ ++ K ⊗ K' ∷ Δ₁) [] I = refl
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.(Γ₀ ++ I ∷ [])} {K = K} {K'} (Ic .(Γ₁ ++ K ∷ K' ∷ Δ₁ ++ x ∷ x₁ ∷ Γ₀) Δ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (K ∷ K' ∷ Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Γ₁ [] I | cases++-inj₂ (K ∷ K' ∷ Δ₁ ++ x ∷ x₁ ∷ Γ₀) Γ₁ [] I | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ K ⊗ K' ∷ Δ₁) [] I =
  cong (Ic (Γ₁ ++ K ⊗ K' ∷ Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ) (⊗cC⊗cC' f refl)
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (⊗c Γ Δ _ _ f) eq with cases++ Γ (Γ₁ ++ _ ∷ _ ∷ Δ₁) [] (_ ∷ _ ∷ Λ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (⊗c .(Γ₁ ++ _ ∷ _ ∷ Δ₁ ++ x ∷ Γ₀) Δ _ _ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.[]} {K = K} {K'} (⊗c .(Γ₁ ++ K ∷ K' ∷ Δ₁ ++ x ∷ []) Δ {J = J}{J'}_ _ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (K ∷ K' ∷ Δ₁) Γ₁ [] (x ⊗ (J ⊗ J')) | cases++-inj₂ (K ∷ K' ∷ Δ₁ ++ x ∷ []) Γ₁ [] (J ⊗ J') | cases++-inj₂ (x ∷ []) (Γ₁ ++ K ⊗ K' ∷ Δ₁) [] (J ⊗ J') = refl
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.(Γ₀ ++ _ ⊗ _ ∷ [])} {K = K} {K'} (⊗c .(Γ₁ ++ K ∷ K' ∷ Δ₁ ++ x ∷ x₁ ∷ Γ₀) Δ {J = J}{J'} _ _ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (K ∷ K' ∷ Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') | cases++-inj₂ (K ∷ K' ∷ Δ₁ ++ x ∷ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ K ⊗ K' ∷ Δ₁) [] (J ⊗ J') =
  cong (⊗c (Γ₁ ++ K ⊗ K' ∷ Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ _ _) (⊗cC⊗cC' f refl)
⊗cC⊗cC' {Γ = Γ} {Δ = Δ} (switch f) eq = ⊥-elim ([]disj∷ (Γ ++ _ ∷ _ ∷ Δ) eq)

⊗cC⊗cC : {S : Stp} {Γ Δ Λ Π : Cxt} {C J J' K K' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → {cK : isCl K} {cK' : isCl K'}
    → (f : S ∣ Γ ++ K ∷ K' ∷ Δ ++ J ∷ J' ∷ Λ ； Π ⊢C C)
    → ⊗cC Γ {Δ ++ _ ∷ Λ} cK cK' (⊗cC (Γ ++ K ∷ K' ∷ Δ) {Λ} cJ cJ' f)
          ≡ ⊗cC (Γ ++ _ ∷ Δ) cJ cJ' (⊗cC Γ {Δ ++ _ ∷ _ ∷ Λ} cK cK' f)
⊗cC⊗cC f = ⊗cC⊗cC' f refl

ufCIcC1 : {Γ Δ : Cxt} {C : Fma}
  → (f : nothing ∣ Γ ； Δ ⊢C C)
  → ufC (IlC f) ≡ IcC [] f
ufCIcC1 (act Γ nA f) =
  cong (act (I ∷ Γ) nA) (ufCIcC1 f)
ufCIcC1 (Ic Γ _ f) =
  cong (Ic (I ∷ Γ) _) (ufCIcC1 f)
ufCIcC1 (⊗c Γ _ _ _ f) =
  cong (⊗c (_ ∷ Γ) _ _ _) (ufCIcC1 f)
ufCIcC1 (switch f) = refl

ufC⊗cC1' : {Γ Γ' Δ : Cxt} {C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : just J ∣ Γ' ； Δ ⊢C C)
  → (eq : Γ' ≡ J' ∷ Γ)
  → ufC (⊗lC (subst (λ x → just J ∣ x ； Δ ⊢C C) eq f)) ≡ ⊗cC' [] cJ cJ' (ufC f) (cong (J ∷_) eq)
ufC⊗cC1' {cJ' = cJ'} (act [] nA f) refl = ⊥-elim (nA cJ')
ufC⊗cC1' (act (x ∷ Γ) nA f) refl = cong (act (_ ⊗ x ∷ Γ) nA) (ufC⊗cC1' f refl)
ufC⊗cC1' {J = J} {cJ = cJ} (Ic [] Δ f) refl rewrite isCl-eq (is⊗ cJ isI) = refl
ufC⊗cC1' (Ic (x ∷ Γ) Δ f) refl = cong (Ic (_ ⊗ x ∷ Γ) Δ) (ufC⊗cC1' f refl)
ufC⊗cC1' {cJ = cJ₁} (⊗c [] Δ cJ cJ' f) refl rewrite isCl-eq (is⊗ cJ₁ (is⊗ cJ cJ')) = refl
ufC⊗cC1' (⊗c (x ∷ Γ) Δ cJ cJ' f) refl = cong (⊗c (_ ⊗ x ∷ Γ) Δ cJ cJ') (ufC⊗cC1' f refl)

ufC⊗cC1 : {Γ Δ : Cxt} {C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : just J ∣ J' ∷ Γ ； Δ ⊢C C)
  → ufC (⊗lC f) ≡ ⊗cC [] cJ cJ' (ufC f)
ufC⊗cC1 f = ufC⊗cC1' f refl

ufCIcC'2 : {Γ Γ' Δ Λ : Cxt} {A C : Fma}
  → (f : just A ∣ Γ' ； Λ ⊢C C)
  → (eq : Γ' ≡ Γ ++ Δ)
  → ufC (IcC' Γ {Δ} f eq) ≡ IcC' (A ∷ Γ) (ufC f) (cong (A ∷_) eq)
ufCIcC'2 {Γ₁} {Δ = Δ} (act Γ nA f) eq with cases++ Γ Γ₁ [] Δ (sym eq)
ufCIcC'2 {.(Γ ++ A ∷ [])} {Δ = .[]} (act Γ {A = A} nA f) refl | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Γ [] [] A = refl
ufCIcC'2 {Γ₁} (act .(Γ₁ ++ Γ₀) {A = A} nA f) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Γ₁ [] A = cong (act (_ ∷ Γ₁ ++ I ∷ Γ₀) nA) (ufCIcC'2 f refl)
ufCIcC'2 {Γ₁} {Δ = Δ} (Ic Γ _ f) eq with cases++ Γ Γ₁ [] Δ (sym eq)
ufCIcC'2 {Δ = .[]} (Ic Γ _ f) refl | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Γ [] [] I = refl
ufCIcC'2 {Γ₁} (Ic _ _ f) refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ Γ₁ [] I = cong (Ic (_ ∷ Γ₁ ++ I ∷ Γ₀) _) (ufCIcC'2 f refl)
ufCIcC'2 {Γ₁} {Δ = Δ} (⊗c Γ _ _ _ f) eq with cases++ Γ Γ₁ [] Δ (sym eq)
ufCIcC'2 {Δ = .[]} (⊗c Γ _ {J = J}{J'} _ _ f) refl | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Γ [] [] (J ⊗ J') = refl
ufCIcC'2 {Γ₁} (⊗c _ _ {J = J}{J'} _ _ f) refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ Γ₁ [] (J ⊗ J') = cong (⊗c (_ ∷ Γ₁ ++ _ ∷ Γ₀) _ _ _) (ufCIcC'2 f refl)
ufCIcC'2 {[]} {Δ = .[]} {A = A} (switch f) refl with isCl? A
ufCIcC'2 {[]} {_} {.[]} {A = A} (switch f) refl | inj₁ x = refl
ufCIcC'2 {[]} {_} {.[]} {A = .I} (switch (Il f)) refl | inj₂ isI = refl
ufCIcC'2 {[]} {_} {.[]} {A = .I} (switch (switch {nothing} () f)) refl | inj₂ isI
ufCIcC'2 {[]} {_} {.[]} {A = .I} (switch (switch {just x} () f)) refl | inj₂ isI
ufCIcC'2 {[]} {_} {.[]} {A = .(_ ⊗ _)} (switch (⊗l x)) refl | inj₂ (is⊗ y y₁) = refl
ufCIcC'2 {[]} {_} {.[]} {A = .(_ ⊗ _)} (switch (switch {nothing} () f)) refl | inj₂ (is⊗ y y₁)
ufCIcC'2 {[]} {_} {.[]} {A = .(_ ⊗ _)} (switch (switch {just x} () f)) refl | inj₂ (is⊗ y y₁)


ufCIcC2 : {Γ Δ Λ : Cxt} {A C : Fma}
  → (f : just A ∣ Γ ++ Δ ； Λ ⊢C C)
  → ufC (IcC Γ {Δ} f) ≡ IcC (A ∷ Γ) (ufC f)
ufCIcC2 f = ufCIcC'2 f refl

ufC⊗cC'2 : {Γ Γ' Δ Λ : Cxt} {A C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : just A ∣ Γ' ； Λ ⊢C C)
  → (eq : Γ' ≡ Γ ++ J ∷ J' ∷ Δ)
  → ufC (⊗cC' Γ {Δ} cJ cJ' f eq) ≡ ⊗cC' (A ∷ Γ) cJ cJ' (ufC f) (cong (A ∷_) eq)
ufC⊗cC'2 {Γ₁} {Δ = Δ} (act Γ nA f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
ufC⊗cC'2 {Γ₁} {Δ = Δ} (act .(Γ₁ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
ufC⊗cC'2 {Γ₁} {Δ = .[]} {cJ' = cJ'} (act .(Γ₁ ++ x ∷ []) nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = ⊥-elim (nA cJ')
ufC⊗cC'2 {Γ₁} {Δ = .(Γ₀ ++ A ∷ [])} (act .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] A = cong (act (_ ∷ Γ₁ ++ x ⊗ x₁ ∷ Γ₀) nA) (ufC⊗cC'2 f refl)
ufC⊗cC'2 {Γ₁} {Δ = Δ₁} (Ic Γ Δ f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
ufC⊗cC'2 {Γ₁} {Δ = Δ₁} (Ic .(Γ₁ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
ufC⊗cC'2 {Γ₁} {Δ = .[]} (Ic .(Γ₁ ++ x ∷ []) Δ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ []) Γ₁ [] I = refl
ufC⊗cC'2 {Γ₁} {Δ = .(Γ₀ ++ I ∷ [])} (Ic .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] I = cong (Ic (_ ∷ Γ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ) (ufC⊗cC'2 f refl)
ufC⊗cC'2 {Γ₁} {Δ = Δ₁} (⊗c Γ Δ _ _ f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
ufC⊗cC'2 {Γ₁} {Δ = Δ₁} (⊗c .(Γ₁ ++ x ∷ Γ₀) Δ _ _ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
ufC⊗cC'2 {Γ₁} {Δ = .[]} (⊗c .(Γ₁ ++ x ∷ []) Δ {J = J}{J'}_ _ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ []) Γ₁ [] (J ⊗ J') = refl
ufC⊗cC'2 {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (⊗c .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ {J = J}{J'} _ _ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') = cong (⊗c (_ ∷ Γ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ _ _) (ufC⊗cC'2 f refl)
ufC⊗cC'2 {Γ} (switch f) eq = ⊥-elim ([]disj∷ Γ eq)

ufC⊗cC2 : {Γ Δ Λ : Cxt} {A C J J' : Fma}
  → {cJ : isCl J} {cJ' : isCl J'}
  → (f : just A ∣ Γ ++ J ∷ J' ∷ Δ ； Λ ⊢C C)
  → ufC (⊗cC Γ {Δ} cJ cJ' f) ≡ ⊗cC (A ∷ Γ) cJ cJ' (ufC f)
ufC⊗cC2 f = ufC⊗cC'2 f refl

focus-compat : {S : Stp} → {Γ : Cxt} → {C : Fma} →
               {f g : S ∣ Γ ⊢ C} → f ≗ g → focus f ≡ focus g
focus-compat refl = refl
focus-compat (~ eq) = sym (focus-compat eq)
focus-compat (eq ∙ eq₁) = trans (focus-compat eq) (focus-compat eq₁)
focus-compat (uf eq) = cong ufC (focus-compat eq)
focus-compat (⊗l eq) = cong ⊗lC (focus-compat eq)
focus-compat (Il eq) = cong IlC (focus-compat eq)
focus-compat (⊗r eq eq₁) = cong₂ ⊗rC (focus-compat eq) (focus-compat eq₁)
focus-compat axI = refl
focus-compat ax⊗ = refl
focus-compat (⊗ruf {f = f}{g}) = ⊗rCufC (focus f) (focus g)
focus-compat (⊗rIl {f = f}{g}) = ⊗rCIlC (focus f) (focus g)
focus-compat (⊗r⊗l {f = f}{g}) = ⊗rC⊗lC (focus f) (focus g)
focus-compat (Ic _ _ eq) = cong (IcC _) (focus-compat eq)
focus-compat (⊗rIc1 {f = f}{g}) = ⊗rCIcC1 (focus f) (focus g)
focus-compat (⊗rIc2 {Γ = Γ}{Δ}{Δ'} {f = f}{g}) =
  ⊗rCIcC2 {Γ = Γ}{Δ}{Δ'} (focus f) (focus g)
focus-compat (IlIc {f = f}) = IlCIcC (focus f)
focus-compat (⊗lIc {f = f}) = ⊗lCIcC (focus f)
focus-compat (IcIc {f = f}) = IcCIcC (focus f)
focus-compat (ufIc1 {f = f}) = ufCIcC1 (focus f)
focus-compat (ufIc2 {f = f}) = ufCIcC2 (focus f)
focus-compat (⊗c Γ Δ cJ cJ' p) = cong (⊗cC Γ cJ cJ') (focus-compat p)
focus-compat (uf⊗c1 {f = f}) = ufC⊗cC1 (focus f)
focus-compat (⊗c⊗c {f = f}) = ⊗cC⊗cC (focus f)
focus-compat (Ic⊗c {f = f}) = IcC⊗cC (focus f)
focus-compat (⊗cIc {f = f}) = ⊗cCIcC (focus f)
focus-compat (uf⊗c2 {f = f}) = ufC⊗cC2 (focus f)
focus-compat (Il⊗c {f = f}) = IlC⊗cC (focus f)
focus-compat (⊗l⊗c {f = f}) = ⊗lC⊗cC (focus f)
focus-compat (⊗r⊗c1 {f = f} {g}) = ⊗rC⊗cC1 (focus f) (focus g)
focus-compat (⊗r⊗c2 {f = f} {g}) = ⊗rC⊗cC2 (focus f) (focus g)
 
-- emb ∘ focus ≗ id


mutual
  embC-⊗rCL : {S : Stp} {Γ Δ Λ : Cxt} → {A B : Fma}
    → (f : S ∣ Γ ； Δ ⊢C A) (g : nothing ∣ Λ ⊢L B)
    → embC (⊗rCL f g) ≗ ⊗r (embC f) (embL g) 
  embC-⊗rCL (act Γ nA f) g = embC-⊗rCL f g
  embC-⊗rCL (Ic Γ _ f) g =
    Ic Γ _ (embC-⊗rCL f g)
    ∙ ~ ⊗rIc1
  embC-⊗rCL (⊗c Γ _ _ _ f) g =
    ⊗c Γ _ _ _ (embC-⊗rCL f g)
    ∙ ~ ⊗r⊗c1
  embC-⊗rCL (switch f) g = embC-⊗rLL f g

  embC-⊗rLL : {S : Stp} {Γ Δ : Cxt} → {A B : Fma}
    → (f : S ∣ Γ  ⊢L A) (g : nothing ∣ Δ ⊢L B)
    → embL (⊗rLL f g) ≗ ⊗r (embL f) (embL g)
  embC-⊗rLL (Il f) g =
    Il (embC-⊗rLL f g) ∙ ~ ⊗rIl
  embC-⊗rLL (⊗l f) g =
    ⊗l (embC-⊗rCL f g) ∙ ~ ⊗r⊗l
  embC-⊗rLL (uf f) g =
    uf (embC-⊗rLL f g) ∙ ~ ⊗ruf
  embC-⊗rLL (switch refl f) g = refl

embC-⊗rC : {S : Stp} {Γ Δ Λ : Cxt} → {A B : Fma}
  → (f : S ∣ Γ ； [] ⊢C A) (g : nothing ∣ Δ ； Λ ⊢C B)
  → embC (⊗rC f g) ≗ ⊗r (embC f) (embC g) 
embC-⊗rC f (act Γ nA g) = embC-⊗rC f g
embC-⊗rC {Γ = Γ₁} f (Ic Γ _ g) =
  Ic (Γ₁ ++ Γ) _ (embC-⊗rC f g)
  ∙ ~ ⊗rIc2 
embC-⊗rC {Γ = Γ₁} f (⊗c Γ _ _ _ g) =
  ⊗c (Γ₁ ++ Γ) _ _ _ (embC-⊗rC f g)
  ∙ ~ ⊗r⊗c2 
embC-⊗rC f (switch g) = embC-⊗rCL f g

embC-ufC : {Γ Δ : Cxt} {A C : Fma}
  → (f : just A ∣ Γ ； Δ ⊢C C)
  → embC (ufC f) ≗ uf (embC f)
embC-ufC (act Γ nA f) = embC-ufC f
embC-ufC {Δ = Δ} {A} (Ic Γ _ f) =
  Ic (A ∷ Γ) _ (embC-ufC f)
  ∙ ~ ufIc2
embC-ufC {Δ = Δ} {A} (⊗c Γ _ _ _ f) =
  ⊗c (A ∷ Γ) _ _ _ (embC-ufC f)
  ∙ ~ uf⊗c2
embC-ufC {A = A} (switch f) with isCl? A
embC-ufC {A = A} (switch f) | inj₁ x = refl
embC-ufC {A = .I} (switch (Il f)) | inj₂ isI = ~ ufIc1
embC-ufC {A = .I} (switch (switch {nothing} () f)) | inj₂ isI
embC-ufC {A = .I} (switch (switch {just x} () f)) | inj₂ isI
embC-ufC {A = .(_ ⊗ _)} (switch (⊗l x)) | inj₂ (is⊗ y y₁) =
  ⊗c [] _ y y₁ (embC-ufC x)
  ∙ ~ uf⊗c1
embC-ufC {A = .(_ ⊗ _)} (switch (switch {nothing} () f)) | inj₂ (is⊗ y y₁)
embC-ufC {A = .(_ ⊗ _)} (switch (switch {just x} () f)) | inj₂ (is⊗ y y₁)

embC-IlC : {Γ Δ : Cxt} → {C : Fma}
  → (f : nothing ∣ Γ ； Δ ⊢C C)
  → embC (IlC f) ≗ Il (embC f)
embC-IlC (act Γ nA f) = embC-IlC f
embC-IlC (Ic Γ _ f) = Ic Γ _ (embC-IlC f) ∙ ~ IlIc
embC-IlC (⊗c Γ _ _ _ f) = ⊗c Γ _ _ _ (embC-IlC f) ∙ ~ Il⊗c
embC-IlC (switch f) = refl

embC-IcC' : {S : Stp} (Γ : Cxt) {Γ' Δ Λ : Cxt} {C : Fma}
  → (f : S ∣ Λ ； Δ ⊢C C) (eq : Λ ≡ Γ ++ Γ')
  → embC (IcC' Γ {Γ'}{Δ} f eq)
    ≗ Ic Γ (Γ' ++ Δ) (subst (λ x → S ∣ x ++ Δ ⊢ C) {y = Γ ++ Γ'} eq (embC f))
embC-IcC' Γ {Γ'} (act Γ₁ nA f) eq with cases++ Γ₁ Γ [] Γ' (sym eq)
embC-IcC' .(Γ₁ ++ _ ∷ []) {.[]} (act Γ₁ nA f) refl | inj₁ ([] , refl , refl) = refl
embC-IcC' Γ {.(Γ₀ ++ _ ∷ [])} (act .(Γ ++ Γ₀) nA f) refl | inj₂ (Γ₀ , refl , refl) = embC-IcC' Γ f refl
embC-IcC' Γ {Γ'} (Ic Γ₁ _ f) eq with  cases++ Γ₁ Γ [] Γ' (sym eq)
embC-IcC' .(Γ₁ ++ I ∷ []) {.[]} (Ic Γ₁ _ f) refl | inj₁ ([] , refl , refl) = refl
embC-IcC' Γ {.(Γ₀ ++ I ∷ [])} (Ic .(Γ ++ Γ₀) _ f) refl | inj₂ (Γ₀ , refl , refl) =
  Ic (Γ ++ I ∷ Γ₀) _ (embC-IcC' Γ f refl)
  ∙ ~ IcIc
embC-IcC' Γ {Γ'} (⊗c Γ₁ _ _ _ f) eq with  cases++ Γ₁ Γ [] Γ' (sym eq)
embC-IcC' .(Γ₁ ++ _ ∷ []) {.[]} (⊗c Γ₁ _ _ _ f) refl | inj₁ ([] , refl , refl) = refl
embC-IcC' Γ {.(Γ₀ ++ _ ∷ [])} (⊗c .(Γ ++ Γ₀) _ _ _ f) refl | inj₂ (Γ₀ , refl , refl) =
  ⊗c (Γ ++ I ∷ Γ₀) _ _ _ (embC-IcC' Γ {Γ₀ ++ _ ∷ _ ∷ []} f refl)
  ∙ ~ Ic⊗c
embC-IcC' [] (switch f) refl = refl

embC-IcC : {S : Stp} (Γ : Cxt) {Γ' Δ : Cxt} {C : Fma}
  → (f : S ∣ Γ ++ Γ' ； Δ ⊢C C)
  → embC (IcC Γ {Γ'}{Δ} f) ≗ Ic Γ (Γ' ++ Δ)(embC f)
embC-IcC Γ f = embC-IcC' Γ f refl

embC-⊗cC' : {S : Stp} (Γ : Cxt) {Γ' Δ Λ : Cxt} {C J J' : Fma}
  → {cJ : isCl J}{cJ' : isCl J'}
  → (f : S ∣ Λ ； Δ ⊢C C) (eq : Λ ≡ Γ ++ J ∷ J' ∷ Γ')
  → embC (⊗cC' Γ {Γ'}{Δ} cJ cJ' f eq)
    ≗ ⊗c Γ (Γ' ++ Δ) cJ cJ' (subst (λ x → S ∣ x ++ Δ ⊢ C) {y = Γ ++ J ∷ J' ∷ Γ'} eq (embC f))
embC-⊗cC' Γ {Γ'} (act Γ₁ nA f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
embC-⊗cC' Γ {Γ'} (act .(Γ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
embC-⊗cC' Γ {.[]} {cJ' = cJ'} (act .(Γ ++ x ∷ []) nA f) refl | inj₂ (x ∷ [] , p , refl) | refl , refl = ⊥-elim (nA cJ')
embC-⊗cC' Γ {.(Γ₀ ++ _ ∷ [])} (act .(Γ ++ x ∷ x₁ ∷ Γ₀) nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , p , refl) | refl , refl =
  embC-⊗cC' Γ f refl
embC-⊗cC' Γ {Γ'} (Ic Γ₁ Δ f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
embC-⊗cC' .(Γ₁ ++ I ∷ Γ₀) {Γ'} (Ic Γ₁ Δ f) eq | inj₁ (Γ₀ , refl , q) = ⊥-elim ([]disj∷ Γ₀ q)
embC-⊗cC' Γ {Γ'} (Ic .(Γ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
embC-⊗cC' Γ {.[]} {cJ' = isI} (Ic .(Γ ++ x ∷ []) Δ f) refl | inj₂ (x ∷ [] , p , refl) | refl , refl = refl
embC-⊗cC' Γ {.(Γ₀ ++ I ∷ [])} (Ic .(Γ ++ x ∷ x₁ ∷ Γ₀) Δ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  Ic (Γ ++ x ⊗ x₁ ∷ Γ₀) _ (embC-⊗cC' Γ f refl)
  ∙ ~ ⊗cIc
embC-⊗cC' Γ {Γ'} (⊗c Γ₁ Δ _ _ f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
embC-⊗cC' .(Γ₁ ++ _ ∷ Γ₀) {Γ'} (⊗c Γ₁ Δ _ _ f) eq | inj₁ (Γ₀ , refl , q) = ⊥-elim ([]disj∷ Γ₀ q)
embC-⊗cC' Γ {Γ'} (⊗c .(Γ ++ x ∷ Γ₀) Δ _ _ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
embC-⊗cC' Γ {.[]} {cJ' = cJ'} (⊗c .(Γ ++ x ∷ []) Δ _ _ f) refl | inj₂ (x ∷ [] , p , refl) | refl , refl =
    ≡-to-≗ (cong (λ x → ⊗c Γ Δ _ x (⊗c (Γ ++ _ ∷ []) Δ _ _ (embC f))) (uniq-cl _ _))
embC-⊗cC' Γ {.(Γ₀ ++ _ ∷ [])} (⊗c .(Γ ++ x ∷ x₁ ∷ Γ₀) Δ _ _ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  ⊗c (Γ ++ x ⊗ x₁ ∷ Γ₀) _ _ _ (embC-⊗cC' Γ f refl)
  ∙ ~ ⊗c⊗c
embC-⊗cC' Γ (switch f) eq = ⊥-elim ([]disj∷ Γ eq)

embC-⊗cC : {S : Stp} (Γ : Cxt) {Γ' Δ : Cxt} {C J J' : Fma}
  → {cJ : isCl J}{cJ' : isCl J'}
  → (f : S ∣ Γ ++ J ∷ J' ∷ Γ' ； Δ ⊢C C)
  → embC (⊗cC Γ {Γ'}{Δ} cJ cJ' f) ≗ ⊗c Γ (Γ' ++ Δ) cJ cJ' (embC f)
embC-⊗cC Γ f = embC-⊗cC' Γ f refl

embC-⊗lC' : {Γ Γ' Δ : Cxt} → {A B C : Fma}
  → (f : just A ∣ Γ' ； Δ ⊢C C) (eq : Γ' ≡ B ∷ Γ)
  → embC (⊗lC' f eq) ≗ ⊗l (subst (λ x → _ ∣ x ++ Δ ⊢ C) eq (embC f))
embC-⊗lC' (act [] nA f) refl = refl
embC-⊗lC' (act (B ∷ Γ) nA f) refl = embC-⊗lC' f refl
embC-⊗lC' (Ic [] _ f) refl = refl
embC-⊗lC' (Ic (B ∷ Γ) _ f) refl =
  Ic Γ _ (embC-⊗lC' f refl)
  ∙ ~ ⊗lIc
embC-⊗lC' (⊗c [] _ _ _ f) refl = refl
embC-⊗lC' (⊗c (B ∷ Γ) _ _ _ f) refl =
  ⊗c Γ _ _ _ (embC-⊗lC' f refl)
  ∙ ~ ⊗l⊗c

embC-⊗lC : {Γ Δ : Cxt} → {A B C : Fma}
  → (f : just A ∣ B ∷ Γ ； Δ ⊢C C)
  → embC (⊗lC f) ≗ ⊗l (embC f)
embC-⊗lC f = embC-⊗lC' f refl

embC-axC : {A : Fma} → embC (axC {A}) ≗ ax
embC-axC {` X} = refl
embC-axC {I} = ~ axI
embC-axC {A₁ ⊗ A₂} =
  embC-⊗lC (⊗rC axC (ufC axC))
  ∙ ⊗l (embC-⊗rC axC (ufC axC)
       ∙ ⊗r embC-axC (embC-ufC axC ∙ uf embC-axC)) 
  ∙ ~ ax⊗

emb-focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
             (f : S ∣ Γ ⊢ C)  → emb (focus f) ≗ f
emb-focus ax = embC-axC
emb-focus (uf f) =
  embC-ufC (focus f)
  ∙ uf (emb-focus f)
emb-focus Ir = refl
emb-focus (⊗r f g) =
  embC-⊗rC (focus f) (focus g)
  ∙ ⊗r (emb-focus f) (emb-focus g)
emb-focus (Il f) =
  embC-IlC (focus f)
  ∙ Il (emb-focus f)
emb-focus (Ic Γ Δ f) =
  embC-IcC Γ (focus f)
  ∙ Ic Γ _ (emb-focus f)
emb-focus (⊗c Γ Δ cJ cJ' f) =
  embC-⊗cC Γ (focus f)
  ∙ ⊗c Γ _ _ _ (emb-focus f)
emb-focus (⊗l f) =
  embC-⊗lC (focus f)
  ∙ ⊗l (emb-focus f)


