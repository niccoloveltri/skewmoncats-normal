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

-- irreducible stoup

StpR : Set
StpR = Maybe At

-- non-compound formula, i.e. not containing tensor

data no-⊗ : Fma → Set where
  is-at : {X : At} → no-⊗ (` X)
  is-I : no-⊗ I

data no-⊗s : Cxt → Set where
  is-[] : no-⊗s []
  is-∷ : {A : Fma} {Γ : Cxt}
    → no-⊗ A → no-⊗s Γ → no-⊗s (A ∷ Γ)

no-⊗s-++ : {Γ Δ : Cxt} → no-⊗s (Γ ++ Δ) → no-⊗s Γ × no-⊗s Δ
no-⊗s-++ {[]} nΔ = is-[] , nΔ
no-⊗s-++ {A ∷ Γ}{Δ} (is-∷ nA nΓΔ) =
  is-∷ nA (no-⊗s-++ {Γ}{Δ} nΓΔ .proj₁) , no-⊗s-++ nΓΔ .proj₂

-- focused sequent calculus

infix 15 _∣_；_⊢C_ _∣_⊢L_ _∣_⊢R_

mutual
  data _∣_；_⊢C_ : Stp → Cxt → Cxt → Fma → Set where
    act : {S : Stp} (Γ : Cxt) {Δ : Cxt} {A C : Fma}
      → (nA : no-⊗ A) (f : S ∣ Γ ； A ∷ Δ ⊢C C)
      → S ∣ Γ ++ A ∷ [] ； Δ ⊢C C
    ⊗c : {S : Stp} (Γ : Cxt) (Δ : Cxt) {C J J' : Fma}
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
IlC (⊗c _ _ f) = ⊗c _ _ (IlC f)
IlC (switch f) = switch (Il f)

⊗lC' : {Γ Γ' Δ : Cxt} → {A B C : Fma} → 
  just A ∣ Γ' ； Δ ⊢C C → Γ' ≡ B ∷ Γ → just (A ⊗ B) ∣ Γ ； Δ ⊢C C
⊗lC' (act [] nA f) refl = switch (⊗l (act _ nA f))
⊗lC' (act (B ∷ Γ) nA f) refl = act _ nA (⊗lC' f refl)
⊗lC' (⊗c [] _ f) refl = switch (⊗l (⊗c [] _ f))
⊗lC' (⊗c (B ∷ Γ) _ f) refl = ⊗c _ _ (⊗lC' f refl)

⊗lC : {Γ Δ : Cxt} → {A B C : Fma} → 
  just A ∣ B ∷ Γ ； Δ ⊢C C → just (A ⊗ B) ∣ Γ ； Δ ⊢C C
⊗lC f = ⊗lC' f refl

⊗lC'-[] : {Γ Δ : Cxt} → {A B C : Fma}
  → (f : just A ∣ Γ ； Δ ⊢C C) (eq : Γ ≡ B ∷ [])
  → ⊗lC' f eq ≡ switch (⊗l (subst (λ x → just A ∣ x ； Δ ⊢C C) eq f))
⊗lC'-[] (act [] nA f) refl = refl
⊗lC'-[] (act (_ ∷ Γ) nA f) eq = ⊥-elim ([]disj∷ Γ (sym (inj∷ eq .proj₂)))
⊗lC'-[] (⊗c [] _ f) refl = refl
⊗lC'-[] (⊗c (_ ∷ Γ) _ f) eq = ⊥-elim ([]disj∷ Γ (sym (inj∷ eq .proj₂)))

⊗lC-[] : {Δ : Cxt} → {A B C : Fma}
  → (f : just A ∣ B ∷ [] ； Δ ⊢C C) 
  → ⊗lC f ≡ switch (⊗l f)
⊗lC-[] f = ⊗lC'-[]  f refl

ufC : {Γ Δ : Cxt} {A C : Fma}
  → just A ∣ Γ ； Δ ⊢C C → nothing ∣ A ∷ Γ ； Δ ⊢C C
ufC (act _ nA f) = act _ nA (ufC f)
ufC (⊗c Γ Δ f) = ⊗c (_ ∷ Γ) Δ (ufC f)
ufC {A = ` X} (switch f) = act [] is-at (switch (uf f))
ufC {A = I} (switch f) = act [] is-I (switch (uf f))
ufC {A = A ⊗ B} (switch (⊗l f)) = ⊗c [] _ (ufC f)
ufC {A = A ⊗ B} (switch (switch {nothing} () f))
ufC {A = A ⊗ B} (switch (switch {just x} () f))

ufC-switch : {Γ : Cxt} {A C : Fma}
  → (f : just A ∣ Γ ⊢L C) (nA : no-⊗ A)
  → ufC (switch f) ≡ act [] nA (switch (uf f))
ufC-switch f is-at = refl
ufC-switch f is-I = refl

⊗cC' : {S : Stp} (Γ : Cxt) {Γ' Δ Λ : Cxt} {C J J' : Fma}
  → (f : S ∣ Λ ； Δ ⊢C C) → Λ ≡ Γ ++ J ∷ J' ∷ Γ' 
  → S ∣ Γ ++ J ⊗ J' ∷ Γ' ； Δ  ⊢C C
⊗cC' Γ {Γ'} (act Λ nA f) eq with cases++ Λ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC' Γ {Γ'} (act .(Γ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗cC' Γ {.[]} (act .(Γ ++ x ∷ []) nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl =
  ⊗c Γ _ (act (Γ ++ _ ∷ []) nA f)
⊗cC' Γ {.(Γ₀ ++ _ ∷ [])} (act .(Γ ++ x ∷ x₁ ∷ Γ₀) nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  act (Γ ++ _ ∷ Γ₀) nA (⊗cC' Γ f refl)
⊗cC' Γ {Γ'} (⊗c Λ _ f) eq with cases++ Λ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC' Γ {Γ'} (⊗c .(Γ ++ J ∷ Γ₀) _ f) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗cC' Γ {.[]} (⊗c .(Γ ++ J ∷ []) _ f) eq | inj₂ (J ∷ [] , p , refl) | refl , refl =
  ⊗c Γ _ (⊗c (Γ ++ J ∷ []) _ f)
⊗cC' Γ {Γ'} (⊗c .(Γ ++ J ∷ J' ∷ Γ₀) _ f) eq | inj₂ (J ∷ J' ∷ Γ₀ , refl , refl) | refl , r =
  ⊗c (Γ ++ J ⊗ J' ∷ Γ₀) _ (⊗cC' Γ f refl)
⊗cC' Γ (switch f) eq = ⊥-elim ([]disj∷ Γ eq)

⊗cC : {S : Stp} (Γ : Cxt) {Γ' Δ : Cxt} {C J J' : Fma}
  → (f : S ∣ Γ ++ J ∷ J' ∷ Γ' ； Δ ⊢C C)
  → S ∣ Γ ++ J ⊗ J' ∷ Γ' ； Δ  ⊢C C
⊗cC Γ f = ⊗cC' Γ f refl

⊗cC'-[] : {S : Stp} (Γ : Cxt) {Δ Γ' : Cxt} {C J J' : Fma}
  → (f : S ∣ Γ' ； Δ ⊢C C) (eq : Γ' ≡ Γ ++ J ∷ J' ∷ [])
  → ⊗cC' Γ {[]} f eq ≡ ⊗c Γ _ (subst (λ x → S ∣ x ； Δ ⊢C C) eq f)
⊗cC'-[] Γ (act Γ₁ nA f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ []) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC'-[] Γ (act .(Γ ++ J ∷ Γ₀) nA f) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗cC'-[] Γ (act .(Γ ++ J ∷ []) nA f) refl | inj₂ (J ∷ [] , refl , refl) | refl , refl = refl
⊗cC'-[] Γ (act .(Γ ++ J ∷ x ∷ Γ₀) nA f) eq | inj₂ (J ∷ x ∷ Γ₀ , p , refl) | refl , r = ⊥-elim ([]disj∷ Γ₀ (inj∷ r .proj₂))
⊗cC'-[] Γ (⊗c Γ₁ Δ f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ []) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC'-[] Γ (⊗c .(Γ ++ J ∷ Γ₀) Δ f) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗cC'-[] Γ (⊗c .(Γ ++ J ∷ []) Δ f) refl | inj₂ (J ∷ [] , p , refl) | refl , refl = refl
⊗cC'-[] Γ (⊗c .(Γ ++ J ∷ x ∷ Γ₀) Δ f) eq | inj₂ (J ∷ x ∷ Γ₀ , p , refl) | refl , r = ⊥-elim ([]disj∷ Γ₀ (inj∷ r .proj₂))
⊗cC'-[] Γ (switch f) eq =  ⊥-elim ([]disj∷ Γ eq) 

mutual
  ⊗rCL : {S : Stp} → {Γ Δ Λ : Cxt} → {A B : Fma}
    → S ∣ Γ ； Δ ⊢C A → nothing ∣ Λ ⊢L B
    → S ∣ Γ ； Δ ++ Λ ⊢C A ⊗ B
  ⊗rCL (act _ nA f) g = act _ nA (⊗rCL f g)
  ⊗rCL (⊗c _ _ f) g = ⊗c _ _ (⊗rCL f g)
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
⊗rC {Γ = Γ} f (⊗c Γ' _ g) = ⊗c (Γ ++ Γ') _ (⊗rC f g)
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
  embC (⊗c Γ _ f) = ⊗c Γ _ (embC f)
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
focus (⊗c Γ Δ f) = ⊗cC Γ (focus f)

-- A more general act rule, moving multiple formulae out of the
-- anteroom in one single go.

act⋆ : {S : Stp} (Γ : Cxt) {Δ Δ' : Cxt} {C : Fma}
  → (nΔ : no-⊗s Δ)
  → (f : S ∣ Γ ； Δ ++ Δ' ⊢C C)
  → S ∣ Γ ++ Δ ； Δ' ⊢C C
act⋆ Γ is-[] f = f
act⋆ Γ {Δ' = Δ'} (is-∷ {A} nA nΔ) f =
  act⋆ (Γ ++ A ∷ []) nΔ (act Γ nA f)

-- Interaction of act⋆ with other admissible rules

act⋆act⋆ : {S : Stp} (Γ : Cxt) {Δ Δ' Δ'' : Cxt} {C : Fma}
  → (nΔΔ' : no-⊗s (Δ ++ Δ'))
  → (f : S ∣ Γ ； Δ ++ Δ' ++ Δ'' ⊢C C)
  → act⋆ (Γ ++ Δ){Δ'} (no-⊗s-++ nΔΔ' .proj₂)
       (act⋆ Γ {Δ} (no-⊗s-++ {Δ}{Δ'} nΔΔ' .proj₁) f)
    ≡ act⋆ Γ {Δ = Δ ++ Δ'}{Δ''} nΔΔ' f
act⋆act⋆ Γ {[]} nΔ f = refl
act⋆act⋆ Γ {A ∷ Δ} (is-∷ nA nΔΔ') f =
  act⋆act⋆ (Γ ++ A ∷ []) {Δ} nΔΔ' (act Γ nA f)

act⋆-⊗cC : {S : Stp} {Γ Γ' Δ' Δ : Cxt} {C J J' : Fma}
  → (nΔ : no-⊗s Δ) (f : S ∣ Γ ++ J ∷ J' ∷ Γ' ； Δ ++ Δ' ⊢C C)
  → ⊗cC Γ {Γ' ++ Δ}{Δ'} (act⋆ (Γ ++ _ ∷ _ ∷ Γ') nΔ f)
     ≡ act⋆ (Γ ++ _ ∷ Γ') nΔ (⊗cC Γ f)
act⋆-⊗cC is-[] f = refl
act⋆-⊗cC {Γ = Γ} {Γ'} {J = J}{J'} (is-∷ {A} nA nΔ) f = 
  trans (act⋆-⊗cC {Γ = Γ}{Γ' ++ _ ∷ []} nΔ (act (Γ ++ _ ∷ _ ∷ Γ') nA f))
    lem
  where
    lem : act⋆ (Γ ++ _ ∷ Γ' ++ _ ∷ []) nΔ (⊗cC Γ (act (Γ ++ _ ∷ _ ∷ Γ') nA f))
          ≡ act⋆ (Γ ++ _ ∷ Γ' ++ _ ∷ []) nΔ (act (Γ ++ _ ∷ Γ') nA (⊗cC Γ f))
    lem rewrite cases++-inj₂ (J ∷ J' ∷ Γ') Γ [] A = refl

act⋆-IlC : {Γ Δ' Δ : Cxt} {C : Fma}
  → (nΔ : no-⊗s Δ) (f : nothing ∣ Γ ； Δ ++ Δ' ⊢C C)
  → IlC {Γ ++ Δ}{Δ'} (act⋆ Γ nΔ f) ≡ act⋆ Γ nΔ (IlC f)
act⋆-IlC is-[] f = refl
act⋆-IlC {Γ} (is-∷ {A} nA nΔ) f =
  act⋆-IlC {Γ ++ A ∷ []} nΔ (act Γ nA f)  

act⋆-⊗lC : {Γ Δ' Δ : Cxt} {A B C : Fma}
  → (nΔ : no-⊗s Δ) (f : just A ∣ B ∷ Γ ； Δ ++ Δ' ⊢C C)
  → ⊗lC (act⋆ (B ∷ Γ) {_}{Δ'} nΔ f)
     ≡ act⋆ Γ nΔ (⊗lC f)
act⋆-⊗lC is-[] f = refl
act⋆-⊗lC {Γ} (is-∷ {A} nA nΔ) f =
  act⋆-⊗lC {Γ ++ A ∷ []} nΔ (act (_ ∷ Γ) nA f)  

act⋆-ufC : {Γ Δ' Δ : Cxt} {A C : Fma}
  → (nΔ : no-⊗s Δ) (f : just A ∣ Γ ； Δ ++ Δ' ⊢C C)
  → ufC {Γ ++ Δ}{Δ'} (act⋆ Γ nΔ f) ≡ act⋆ (A ∷ Γ) nΔ (ufC f)
act⋆-ufC is-[] f = refl
act⋆-ufC {Γ} (is-∷ {A} nA nΔ) f =
  act⋆-ufC {Γ ++ A ∷ []} nΔ (act Γ nA f)  


act-⊗rCL : {S : Stp} → {Γ Δ Δ' Λ : Cxt} → {A B : Fma}
  → (f : S ∣ Γ ； Δ ++ Δ' ⊢C A) (g : nothing ∣ Λ ⊢L B)
  → (nΔ : no-⊗s Δ)
  → ⊗rCL (act⋆ Γ {Δ' = Δ'} nΔ f) g ≡ act⋆ Γ nΔ (⊗rCL f g)
act-⊗rCL f g is-[] = refl
act-⊗rCL {Γ = Γ} f g (is-∷ {A} nA nΔ) =
  act-⊗rCL {Γ = Γ ++ A ∷ []} (act Γ nA f) g nΔ

act-⊗rC : {S : Stp} → {Γ Δ Λ Λ' : Cxt} → {A B : Fma}
  → (f : S ∣ Γ ； [] ⊢C A) (g : nothing ∣ Δ ； Λ ++ Λ' ⊢C B)
  → (nΛ : no-⊗s Λ)
  → ⊗rC {Λ = Λ'} f (act⋆ Δ nΛ g) ≡ act⋆ (Γ ++ Δ) nΛ (⊗rC f g)
act-⊗rC f g is-[] = refl
act-⊗rC {Γ = Γ} {Δ} f g (is-∷ {A} nA nΛ) =
  act-⊗rC {Γ = Γ}{Δ ++ A ∷ []} f (act Δ nA g) nΛ

-- focus ∘ emb ≡ id

mutual 
  focus-embC : {S : Stp} → {Γ Δ : Cxt} → {C : Fma}
    → (nΔ : no-⊗s Δ) (f : S ∣ Γ ； Δ ⊢C C)
    → focus (embC f) ≡ act⋆ Γ nΔ f
  focus-embC nΔ (act Γ nA f) = focus-embC (is-∷ nA nΔ) f
  focus-embC nΔ (⊗c Γ _ f) =
    trans (cong (λ x → ⊗cC' Γ x refl) (focus-embC nΔ f))
      (trans (act⋆-⊗cC nΔ f)
        (cong (act⋆ (Γ ++ _ ∷ []) nΔ) (⊗cC'-[] Γ f refl)))
  focus-embC nΔ (switch f) = focus-embL nΔ f

  focus-embL : {S : Stp} → {Γ : Cxt} → {C : Fma}
    → (nΓ : no-⊗s Γ) (f : S ∣ Γ ⊢L C)
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
    → (f : S ∣ Γ ⊢R C) (nΓ : no-⊗s Γ)
    → focus (embR f) ≡ act⋆ [] nΓ (switch (switch refl f))
  focus-embR ax is-[] = refl
  focus-embR Ir is-[] = refl
  focus-embR (⊗r {Γ = Γ} {Δ} f g) nΓΔ =
    trans (cong₂ ⊗rC (focus-embR f (no-⊗s-++ {Γ}{Δ} nΓΔ .proj₁))
                     (focus-embL (no-⊗s-++ {Γ}{Δ} nΓΔ .proj₂) g))
      (trans (act-⊗rC (act⋆ []
                            (no-⊗s-++ {Γ}{Δ} nΓΔ .proj₁)
                            (switch (switch refl f)))
                      (switch g)
                      (no-⊗s-++ {Γ}{Δ} nΓΔ .proj₂))
        (trans (cong (act⋆ Γ (no-⊗s-++ {Γ}{Δ} nΓΔ .proj₂))
                     (act-⊗rCL (switch (switch refl f))
                               g
                               (no-⊗s-++ {Γ}{Δ} nΓΔ .proj₁)))
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
⊗rCLufC {A' = A'} (⊗c Γ _ f) g =
  cong (⊗c (A' ∷ Γ) _) (⊗rCLufC f g)
⊗rCLufC {A' = ` X} (switch f) g = refl
⊗rCLufC {A' = I} (switch f) g = refl
⊗rCLufC {A' = A' ⊗ A''} (switch (⊗l f)) g =
  cong (⊗c [] _) (⊗rCLufC f g)
⊗rCLufC {A' = A' ⊗ A''} (switch (switch {nothing} () f)) g
⊗rCLufC {A' = A' ⊗ A''} (switch (switch {just x} () f)) g

⊗rCufC : {Γ Δ Λ : Cxt}{A A' B : Fma}
  → (f : just A' ∣ Γ ； [] ⊢C A)(g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (ufC f) g ≡ ufC (⊗rC f g)
⊗rCufC {Γ₁} {A' = A'} f (act Γ nA g) =
  cong (act (A' ∷ Γ₁ ++ Γ) nA) (⊗rCufC f g)
⊗rCufC {Γ₁} {A' = A'} f (⊗c Γ _ g) =
  cong (⊗c (A' ∷ Γ₁ ++ Γ) _) (⊗rCufC f g)
⊗rCufC f (switch g) = ⊗rCLufC f g

⊗rCLIlC : {Γ Δ Λ : Cxt}{A B : Fma}
  → (f : nothing ∣ Γ ； Δ ⊢C A)(g : nothing ∣ Λ ⊢L B)
  → ⊗rCL (IlC f) g ≡ IlC (⊗rCL f g)
⊗rCLIlC (act Γ nA f) g = cong (act Γ nA) (⊗rCLIlC f g)
⊗rCLIlC (⊗c Γ _ f) g = cong (⊗c Γ _) (⊗rCLIlC f g)
⊗rCLIlC (switch f) g = refl

⊗rCIlC : {Γ Δ Λ : Cxt}{A B : Fma}
  → (f : nothing ∣ Γ ； [] ⊢C A)(g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (IlC f) g ≡ IlC (⊗rC f g)
⊗rCIlC {Γ₁} f (act Γ nA g) = cong (act (Γ₁ ++ Γ) nA) (⊗rCIlC f g)
⊗rCIlC {Γ₁} f (⊗c Γ _ g) = cong (⊗c (Γ₁ ++ Γ) _) (⊗rCIlC f g)
⊗rCIlC f (switch g) = ⊗rCLIlC f g

⊗rCL⊗lC : {Γ Γ' Δ Λ : Cxt}{A A' B B' : Fma}
  → (f : just A' ∣ Γ' ； Δ ⊢C A)(g : nothing ∣ Λ ⊢L B)
  → (eq : Γ' ≡ B' ∷ Γ)
  → ⊗rCL (⊗lC' f eq) g ≡ ⊗lC' (⊗rCL f g) eq
⊗rCL⊗lC (act [] nA f) g refl = refl
⊗rCL⊗lC (act (B ∷ Γ) nA f) g refl = cong (act Γ nA) (⊗rCL⊗lC f g refl)
⊗rCL⊗lC (⊗c [] _ f) g refl = refl
⊗rCL⊗lC (⊗c (B ∷ Γ) _ f) g refl = cong (⊗c Γ _) (⊗rCL⊗lC f g refl)

⊗rC⊗lC : {Γ Δ Λ : Cxt}{A A' B B' : Fma}
  → (f : just A' ∣ B' ∷ Γ ； [] ⊢C A)(g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (⊗lC f) g ≡ ⊗lC (⊗rC f g)
⊗rC⊗lC {Γ₁} f (act Γ nA g) = cong (act (Γ₁ ++ Γ) nA) (⊗rC⊗lC f g)
⊗rC⊗lC {Γ₁} f (⊗c Γ _ g) = cong (⊗c (Γ₁ ++ Γ) _) (⊗rC⊗lC f g)
⊗rC⊗lC f (switch g) = ⊗rCL⊗lC f g refl

⊗rCL⊗cC1 : {S : Stp}{Γ Γ' Γ'' Δ Λ : Cxt}{A B J J' : Fma}
  → (f : S ∣ Γ'' ； Δ ⊢C A) (g : nothing ∣ Λ ⊢L B)
  → (eq : Γ'' ≡ Γ ++ J ∷ J' ∷ Γ')
  → ⊗rCL (⊗cC' Γ {Γ'} f eq) g ≡ ⊗cC' Γ (⊗rCL f g) eq
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (act Γ nA f) g eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (act .(Γ₁ ++ x ∷ Γ₀) nA f) g eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗rCL⊗cC1 {Γ = Γ₁} {.[]} (act .(Γ₁ ++ x ∷ []) nA f) g refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = refl
⊗rCL⊗cC1 {Γ = Γ₁} {.(Γ₀ ++ _ ∷ [])} (act .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) nA f) g refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (act (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) nA) (⊗rCL⊗cC1 f g refl)
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (⊗c Γ Δ f) g eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rCL⊗cC1 {Γ = Γ₁} {Γ'} (⊗c .(Γ₁ ++ x ∷ Γ₀) Δ f) g eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗rCL⊗cC1 {Γ = Γ₁} {.[]} (⊗c .(Γ₁ ++ x ∷ []) Δ f) g refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = refl
⊗rCL⊗cC1 {Γ = Γ₁} {.(Γ₀ ++ _ ∷ [])} (⊗c .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ f) g refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (⊗c (Γ₁ ++ _ ⊗ _ ∷ Γ₀) _) (⊗rCL⊗cC1 f g refl)
⊗rCL⊗cC1 {Γ = Γ} (switch f) g eq = ⊥-elim ([]disj∷ Γ eq)


⊗rC⊗cC1 : {S : Stp}{Γ Γ' Δ Λ : Cxt}{A B J J' : Fma}
  → (f : S ∣ Γ ++ J ∷ J' ∷ Γ' ； [] ⊢C A) (g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (⊗cC Γ {Γ'} f) g ≡ ⊗cC Γ (⊗rC f g)
⊗rC⊗cC1 {Γ = Γ₁} {Γ'} {J = J} {J'} f (act Γ {A = A} nA g)
  rewrite cases++-inj₂ (J ∷ J' ∷ Γ' ++ Γ) Γ₁ [] A =
  cong (act (Γ₁ ++ J ⊗ J' ∷ Γ' ++ Γ) nA) (⊗rC⊗cC1 f g)
⊗rC⊗cC1 {Γ = Γ₁} {Γ'} {J = J} {J'} f (⊗c Γ Δ {J = K} {K'} g) 
  rewrite cases++-inj₂ (J ∷ J' ∷ Γ' ++ Γ) Γ₁ [] (K ⊗ K') =
  cong (⊗c (Γ₁ ++ J ⊗ J' ∷ Γ' ++ Γ) _) (⊗rC⊗cC1 f g)
⊗rC⊗cC1 f (switch f₁) = ⊗rCL⊗cC1 f f₁ refl

⊗rC⊗cC'2 : {S : Stp}{Γ Δ Δ' Δ'' Λ : Cxt}{A B J J' : Fma}
  → (f : S ∣ Γ ； [] ⊢C A) (g : nothing ∣ Δ'' ； Λ ⊢C B)
  → (eq : Δ'' ≡ Δ ++ J ∷ J' ∷ Δ')
  → ⊗rC f (⊗cC' Δ {Δ'} g eq) ≡ ⊗cC' (Γ ++ Δ) (⊗rC f g) (cong (Γ ++_) eq)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ} {Δ'} f (act Γ nA g) eq with cases++ Γ Δ [] (_ ∷ _ ∷ Δ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ} {Δ'} f (act .(Δ ++ x ∷ Γ₀) nA g) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗rC⊗cC'2 {Γ = Γ₁} {Δ} {.[]} f (act .(Δ ++ x ∷ []) {A = A} nA g) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ []) (Γ₁ ++ Δ) [] A = refl
⊗rC⊗cC'2 {Γ = Γ₁} {Δ} {.(Γ₀ ++ A ∷ [])} f (act .(Δ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA g) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ Δ) [] A = 
  cong (act (Γ₁ ++ Δ ++ x ⊗ x₁ ∷ Γ₀) nA) (⊗rC⊗cC'2 f g refl)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {Δ'} {A = A} f (⊗c Γ Δ g) eq with cases++ Γ Δ₁ [] (_ ∷ _ ∷ Δ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {Δ'} {A = A} f (⊗c .(Δ₁ ++ J ∷ Γ₀) Δ g) eq | inj₂ (J ∷ Γ₀ , p , refl) with inj∷ p
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {.[]} {A = A} f (⊗c .(Δ₁ ++ J ∷ []) Δ {J = K}{K'} g) refl | inj₂ (J ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (J ∷ []) (Γ₁ ++ Δ₁) [] (K ⊗ K') = refl
⊗rC⊗cC'2 {Γ = Γ₁} {Δ₁} {.(Γ₀ ++ _ ∷ [])} {A = A} f (⊗c .(Δ₁ ++ J ∷ x ∷ Γ₀) Δ {J = K}{K'} g) refl | inj₂ (J ∷ x ∷ Γ₀ , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (J ∷ x ∷ Γ₀) (Γ₁ ++ Δ₁) [] (K ⊗ K') =
  cong (⊗c (Γ₁ ++ Δ₁ ++ J ⊗ x ∷ Γ₀) Δ) (⊗rC⊗cC'2 f g refl)
⊗rC⊗cC'2 {Δ = Δ} f (switch f₁) eq = ⊥-elim ([]disj∷ Δ eq)

⊗rC⊗cC2 : {S : Stp}{Γ Δ Δ' Λ : Cxt}{A B J J' : Fma}
  → (f : S ∣ Γ ； [] ⊢C A) (g : nothing ∣ Δ ++ J ∷ J' ∷ Δ' ； Λ ⊢C B)
  → ⊗rC f (⊗cC Δ {Δ'} g) ≡ ⊗cC (Γ ++ Δ) (⊗rC f g)
⊗rC⊗cC2 f g = ⊗rC⊗cC'2 f g refl

IlC⊗cC' : {Γ Γ' Δ Λ : Cxt} {C J J' : Fma}
  → (f : nothing ∣ Γ' ； Λ ⊢C C)
  → (eq : Γ' ≡ Γ ++ J ∷ J' ∷ Δ)
  → IlC (⊗cC' Γ {Δ} f eq) ≡ ⊗cC' Γ (IlC f) eq
IlC⊗cC' {Γ₁} {Δ = Δ} (act Γ nA f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
IlC⊗cC' {Γ₁} {Δ = Δ} (act .(Γ₁ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
IlC⊗cC' {Γ₁} {Δ = .[]} (act .(Γ₁ ++ x ∷ []) nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = refl
IlC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (act .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (act (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) nA) (IlC⊗cC' f refl)
IlC⊗cC' {Γ₁} {Δ = Δ₁} (⊗c Γ Δ f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
IlC⊗cC' {Γ₁} {Δ = Δ₁} (⊗c .(Γ₁ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
IlC⊗cC' {Γ₁} {Δ = .[]} (⊗c .(Γ₁ ++ x ∷ []) Δ f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = refl
IlC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (⊗c .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  cong (⊗c (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) _) (IlC⊗cC' f refl)
IlC⊗cC' {Γ} (switch f) eq = ⊥-elim ([]disj∷ Γ eq)

IlC⊗cC : {Γ Δ Λ : Cxt} {C J J' : Fma}
  → (f : nothing ∣ Γ ++ J ∷ J' ∷ Δ ； Λ ⊢C C)
  → IlC (⊗cC Γ {Δ} f) ≡ ⊗cC Γ (IlC f)
IlC⊗cC f = IlC⊗cC' f refl

⊗lC⊗cC' : {Γ Γ' Δ Λ : Cxt} {A B C J J' : Fma}
    → (f : just A ∣ Γ' ； Λ ⊢C C)
    → (eq : Γ' ≡ B ∷ Γ ++ J ∷ J' ∷ Δ)
    → ⊗lC' (⊗cC' (B ∷ Γ) {Δ} f eq) refl ≡ ⊗cC' Γ (⊗lC' f eq) refl
⊗lC⊗cC' {Γ₁} {Δ = Δ} (act Γ nA f) eq with cases++ Γ (_ ∷ Γ₁) [] (_ ∷ _ ∷ Δ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗lC⊗cC' {Γ₁} {Δ = Δ} (act .(_ ∷ Γ₁ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗lC⊗cC' {Γ₁} {Δ = .[]} (act .(_ ∷ Γ₁ ++ x ∷ []) {A = A} nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ []) Γ₁ [] A = refl
⊗lC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ A ∷ [])} (act .(_ ∷ Γ₁ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] A =
    cong (act (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) nA) (⊗lC⊗cC' f refl)
⊗lC⊗cC' {Γ₁} {Δ = Δ₁} (⊗c Γ Δ f) eq with cases++ Γ (_ ∷ Γ₁) [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗lC⊗cC' {Γ₁} {Δ = Δ₁} (⊗c .(_ ∷ Γ₁ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗lC⊗cC' {Γ₁} {Δ = .[]} (⊗c .(_ ∷ Γ₁ ++ x ∷ []) Δ {J = J}{J'} f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ []) Γ₁ [] (J ⊗ J') = refl
⊗lC⊗cC' {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (⊗c .(_ ∷ Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ {J = J}{J'} f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') =
  cong (⊗c (Γ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ) (⊗lC⊗cC' f refl)

⊗lC⊗cC : {Γ Δ Λ : Cxt} {A B C J J' : Fma}
    → (f : just A ∣ B ∷ Γ ++ J ∷ J' ∷ Δ ； Λ ⊢C C)
    → ⊗lC (⊗cC (B ∷ Γ) {Δ} f) ≡ ⊗cC Γ (⊗lC f)
⊗lC⊗cC f = ⊗lC⊗cC' f refl

⊗cC⊗cC' : {S : Stp} {Γ Γ' Δ Λ Π : Cxt} {C J J' K K' : Fma}
    → (f : S ∣ Γ' ； Π ⊢C C)
    → (eq : Γ' ≡ Γ ++ K ∷ K' ∷ Δ ++ J ∷ J' ∷ Λ)
    → ⊗cC' Γ {Δ ++ _ ∷ Λ} (⊗cC' (Γ ++ K ∷ K' ∷ Δ) {Λ} f eq) refl
          ≡ ⊗cC' (Γ ++ _ ∷ Δ) (⊗cC' Γ {Δ ++ _ ∷ _ ∷ Λ} f eq) refl
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ} {Λ} (act Γ nA f) eq with cases++ Γ (Γ₁ ++ _ ∷ _ ∷ Δ) [] (_ ∷ _ ∷ Λ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ} {Λ} (act .(Γ₁ ++ _ ∷ _ ∷ Δ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ} {.[]} {K = K} {K'} (act .(Γ₁ ++ K ∷ K' ∷ Δ ++ x ∷ []) {A = A} nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (K ∷ K' ∷ Δ) Γ₁ [] (x ⊗ A) | cases++-inj₂ (K ∷ K' ∷ Δ ++ x ∷ []) Γ₁ [] A | cases++-inj₂ (x ∷ []) (Γ₁ ++ K ⊗ K' ∷ Δ) [] A  = refl
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ} {.(Γ₀ ++ A ∷ [])} {K = K} {K'} (act .(Γ₁ ++ K ∷ K' ∷ Δ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (K ∷ K' ∷ Δ ++ x ⊗ x₁ ∷ Γ₀) Γ₁ [] A | cases++-inj₂ (K ∷ K' ∷ Δ ++ x ∷ x₁ ∷ Γ₀) Γ₁ [] A | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ K ⊗ K' ∷ Δ) [] A =
  cong (act (Γ₁ ++ K ⊗ K' ∷ Δ ++ x ⊗ x₁ ∷ Γ₀) nA) (⊗cC⊗cC' f refl)
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (⊗c Γ Δ f) eq with cases++ Γ (Γ₁ ++ _ ∷ _ ∷ Δ₁) [] (_ ∷ _ ∷ Λ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {Λ} (⊗c .(Γ₁ ++ _ ∷ _ ∷ Δ₁ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.[]} {K = K} {K'} (⊗c .(Γ₁ ++ K ∷ K' ∷ Δ₁ ++ x ∷ []) Δ {J = J}{J'} f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (K ∷ K' ∷ Δ₁) Γ₁ [] (x ⊗ (J ⊗ J')) | cases++-inj₂ (K ∷ K' ∷ Δ₁ ++ x ∷ []) Γ₁ [] (J ⊗ J') | cases++-inj₂ (x ∷ []) (Γ₁ ++ K ⊗ K' ∷ Δ₁) [] (J ⊗ J') = refl
⊗cC⊗cC' {Γ = Γ₁} {Δ = Δ₁} {.(Γ₀ ++ _ ⊗ _ ∷ [])} {K = K} {K'} (⊗c .(Γ₁ ++ K ∷ K' ∷ Δ₁ ++ x ∷ x₁ ∷ Γ₀) Δ {J = J}{J'} f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (K ∷ K' ∷ Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') | cases++-inj₂ (K ∷ K' ∷ Δ₁ ++ x ∷ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') | cases++-inj₂ (x ∷ x₁ ∷ Γ₀) (Γ₁ ++ K ⊗ K' ∷ Δ₁) [] (J ⊗ J') =
  cong (⊗c (Γ₁ ++ K ⊗ K' ∷ Δ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ) (⊗cC⊗cC' f refl)
⊗cC⊗cC' {Γ = Γ} {Δ = Δ} (switch f) eq = ⊥-elim ([]disj∷ (Γ ++ _ ∷ _ ∷ Δ) eq)

⊗cC⊗cC : {S : Stp} {Γ Δ Λ Π : Cxt} {C J J' K K' : Fma}
    → (f : S ∣ Γ ++ K ∷ K' ∷ Δ ++ J ∷ J' ∷ Λ ； Π ⊢C C)
    → ⊗cC Γ {Δ ++ _ ∷ Λ} (⊗cC (Γ ++ K ∷ K' ∷ Δ) {Λ} f)
          ≡ ⊗cC (Γ ++ _ ∷ Δ) (⊗cC Γ {Δ ++ _ ∷ _ ∷ Λ} f)
⊗cC⊗cC f = ⊗cC⊗cC' f refl

ufC⊗cC1' : {Γ Γ' Δ : Cxt} {C J J' : Fma}
  → (f : just J ∣ Γ' ； Δ ⊢C C)
  → (eq : Γ' ≡ J' ∷ Γ)
  → ufC (⊗lC (subst (λ x → just J ∣ x ； Δ ⊢C C) eq f)) ≡ ⊗cC' [] (ufC f) (cong (J ∷_) eq)
ufC⊗cC1' (act [] nA f) refl = refl
ufC⊗cC1' (act (x ∷ Γ) nA f) refl = cong (act (_ ⊗ x ∷ Γ) nA) (ufC⊗cC1' f refl)
ufC⊗cC1' (⊗c [] Δ f) refl = refl
ufC⊗cC1' (⊗c (x ∷ Γ) Δ f) refl = cong (⊗c (_ ⊗ x ∷ Γ) Δ) (ufC⊗cC1' f refl)

ufC⊗cC1 : {Γ Δ : Cxt} {C J J' : Fma}
 → (f : just J ∣ J' ∷ Γ ； Δ ⊢C C)
 → ufC (⊗lC f) ≡ ⊗cC [] (ufC f)
ufC⊗cC1 f = ufC⊗cC1' f refl

ufC⊗cC'2 : {Γ Γ' Δ Λ : Cxt} {A C J J' : Fma}
  → (f : just A ∣ Γ' ； Λ ⊢C C)
  → (eq : Γ' ≡ Γ ++ J ∷ J' ∷ Δ)
  → ufC (⊗cC' Γ {Δ} f eq) ≡ ⊗cC' (A ∷ Γ) (ufC f) (cong (A ∷_) eq)
ufC⊗cC'2 {Γ₁} {Δ = Δ} (act Γ nA f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
ufC⊗cC'2 {Γ₁} {Δ = Δ} (act .(Γ₁ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
ufC⊗cC'2 {Γ₁} {Δ = .[]} (act .(Γ₁ ++ x ∷ []) {A = A} nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ []) Γ₁ [] A = refl
ufC⊗cC'2 {Γ₁} {Δ = .(Γ₀ ++ A ∷ [])} (act .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) {A = A} nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] A = cong (act (_ ∷ Γ₁ ++ x ⊗ x₁ ∷ Γ₀) nA) (ufC⊗cC'2 f refl)
ufC⊗cC'2 {Γ₁} {Δ = Δ₁} (⊗c Γ Δ f) eq with cases++ Γ Γ₁ [] (_ ∷ _ ∷ Δ₁) (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
ufC⊗cC'2 {Γ₁} {Δ = Δ₁} (⊗c .(Γ₁ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
ufC⊗cC'2 {Γ₁} {Δ = .[]} (⊗c .(Γ₁ ++ x ∷ []) Δ {J = J}{J'} f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl
  rewrite cases++-inj₂ (x ∷ []) Γ₁ [] (J ⊗ J') = refl
ufC⊗cC'2 {Γ₁} {Δ = .(Γ₀ ++ _ ∷ [])} (⊗c .(Γ₁ ++ x ∷ x₁ ∷ Γ₀) Δ {J = J}{J'} f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Γ₀) Γ₁ [] (J ⊗ J') = cong (⊗c (_ ∷ Γ₁ ++ x ⊗ x₁ ∷ Γ₀) Δ) (ufC⊗cC'2 f refl)
ufC⊗cC'2 {Γ} (switch f) eq = ⊥-elim ([]disj∷ Γ eq)

ufC⊗cC2 : {Γ Δ Λ : Cxt} {A C J J' : Fma}
  → (f : just A ∣ Γ ++ J ∷ J' ∷ Δ ； Λ ⊢C C)
  → ufC (⊗cC Γ {Δ} f) ≡ ⊗cC (A ∷ Γ) (ufC f)
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
focus-compat (⊗c Γ Δ p) = cong (⊗cC Γ) (focus-compat p)
focus-compat (uf⊗c1 {f = f}) = ufC⊗cC1 (focus f)
focus-compat (⊗c⊗c {f = f}) = ⊗cC⊗cC (focus f)
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
  embC-⊗rCL (⊗c Γ _ f) g =
    ⊗c Γ _ (embC-⊗rCL f g)
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
embC-⊗rC {Γ = Γ₁} f (⊗c Γ _ g) =
  ⊗c (Γ₁ ++ Γ) _ (embC-⊗rC f g)
  ∙ ~ ⊗r⊗c2 
embC-⊗rC f (switch g) = embC-⊗rCL f g

embC-ufC : {Γ Δ : Cxt} {A C : Fma}
  → (f : just A ∣ Γ ； Δ ⊢C C)
  → embC (ufC f) ≗ uf (embC f)
embC-ufC (act Γ nA f) = embC-ufC f
embC-ufC {Δ = Δ} {A} (⊗c Γ _ f) =
  ⊗c (A ∷ Γ) _ (embC-ufC f)
  ∙ ~ uf⊗c2
embC-ufC {A = ` X} (switch f) = refl
embC-ufC {A = I} (switch f) = refl
embC-ufC {A = A ⊗ B} (switch (⊗l f)) = 
  ⊗c [] _ (embC-ufC f)
  ∙ ~ uf⊗c1
embC-ufC {A = A ⊗ B} (switch (switch {nothing} () f))
embC-ufC {A = A ⊗ B} (switch (switch {just x} () f))

embC-IlC : {Γ Δ : Cxt} → {C : Fma}
  → (f : nothing ∣ Γ ； Δ ⊢C C)
  → embC (IlC f) ≗ Il (embC f)
embC-IlC (act Γ nA f) = embC-IlC f
embC-IlC (⊗c Γ _ f) = ⊗c Γ _ (embC-IlC f) ∙ ~ Il⊗c
embC-IlC (switch f) = refl

embC-⊗cC' : {S : Stp} (Γ : Cxt) {Γ' Δ Λ : Cxt} {C J J' : Fma}
  → (f : S ∣ Λ ； Δ ⊢C C) (eq : Λ ≡ Γ ++ J ∷ J' ∷ Γ')
  → embC (⊗cC' Γ {Γ'}{Δ} f eq)
    ≗ ⊗c Γ (Γ' ++ Δ) (subst (λ x → S ∣ x ++ Δ ⊢ C) {y = Γ ++ J ∷ J' ∷ Γ'} eq (embC f))
embC-⊗cC' Γ {Γ'} (act Γ₁ nA f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
... | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
embC-⊗cC' Γ {Γ'} (act .(Γ ++ x ∷ Γ₀) nA f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
embC-⊗cC' Γ {.[]} (act .(Γ ++ x ∷ []) nA f) refl | inj₂ (x ∷ [] , refl , refl) | refl , refl = refl
embC-⊗cC' Γ {.(Γ₀ ++ _ ∷ [])} (act .(Γ ++ x ∷ x₁ ∷ Γ₀) nA f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  embC-⊗cC' Γ f refl
embC-⊗cC' Γ {Γ'} (⊗c Γ₁ Δ f) eq with cases++ Γ₁ Γ [] (_ ∷ _ ∷ Γ') (sym eq)
embC-⊗cC' .(Γ₁ ++ _ ∷ Γ₀) {Γ'} (⊗c Γ₁ Δ f) eq | inj₁ (Γ₀ , refl , q) = ⊥-elim ([]disj∷ Γ₀ q)
embC-⊗cC' Γ {Γ'} (⊗c .(Γ ++ x ∷ Γ₀) Δ f) eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
embC-⊗cC' Γ {.[]} (⊗c .(Γ ++ x ∷ []) Δ f) refl | inj₂ (x ∷ [] , p , refl) | refl , refl = refl
embC-⊗cC' Γ {.(Γ₀ ++ _ ∷ [])} (⊗c .(Γ ++ x ∷ x₁ ∷ Γ₀) Δ f) refl | inj₂ (x ∷ x₁ ∷ Γ₀ , refl , refl) | refl , refl =
  ⊗c (Γ ++ x ⊗ x₁ ∷ Γ₀) _ (embC-⊗cC' Γ f refl)
  ∙ ~ ⊗c⊗c
embC-⊗cC' Γ (switch f) eq = ⊥-elim ([]disj∷ Γ eq)

embC-⊗cC : {S : Stp} (Γ : Cxt) {Γ' Δ : Cxt} {C J J' : Fma}
  → (f : S ∣ Γ ++ J ∷ J' ∷ Γ' ； Δ ⊢C C)
  → embC (⊗cC Γ {Γ'}{Δ} f) ≗ ⊗c Γ (Γ' ++ Δ) (embC f)
embC-⊗cC Γ f = embC-⊗cC' Γ f refl

embC-⊗lC' : {Γ Γ' Δ : Cxt} → {A B C : Fma}
  → (f : just A ∣ Γ' ； Δ ⊢C C) (eq : Γ' ≡ B ∷ Γ)
  → embC (⊗lC' f eq) ≗ ⊗l (subst (λ x → _ ∣ x ++ Δ ⊢ C) eq (embC f))
embC-⊗lC' (act [] nA f) refl = refl
embC-⊗lC' (act (B ∷ Γ) nA f) refl = embC-⊗lC' f refl
embC-⊗lC' (⊗c [] _ f) refl = refl
embC-⊗lC' (⊗c (B ∷ Γ) _ f) refl =
  ⊗c Γ _ (embC-⊗lC' f refl)
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
emb-focus (⊗c Γ Δ f) =
  embC-⊗cC Γ (focus f)
  ∙ ⊗c Γ _ (emb-focus f)
emb-focus (⊗l f) =
  embC-⊗lC (focus f)
  ∙ ⊗l (emb-focus f)


