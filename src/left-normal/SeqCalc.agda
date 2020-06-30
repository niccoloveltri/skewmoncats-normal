{-# OPTIONS --rewriting #-}

module SeqCalc where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Fsk

{- ================================================================ -}

-- Focused sequent calculus for left-normal skew monoidal categories

Stp : Set
Stp = Maybe Fma

Cxt : Set
Cxt = List Fma

StpR : Set
StpR = Maybe At

infix 15 _∣_⊢L_ _∣_⊢R_

mutual
  data _∣_⊢L_ : Stp → Cxt → Fma → Set where
    Il : {Γ : Cxt} → {C : Fma} → 
              nothing ∣ Γ ⊢L C → just I ∣ Γ ⊢L C 
    ⊗l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ B ∷ Γ ⊢L C → just (A ⊗ B) ∣ Γ ⊢L C
    uf : {Γ : Cxt} {A C : Fma} → 
              just A ∣ Γ ⊢L C → nothing ∣ A ∷ Γ ⊢L C
    switch-at :  {X : At} {Γ : Cxt} {C : Fma} → 
              (f : just X ∣ Γ ⊢R C) → just (` X) ∣ Γ ⊢L C
    switch-not :  {C : Fma} → 
              (f : nothing ∣ [] ⊢R C) → nothing ∣ [] ⊢L C

  data _∣_⊢R_ : StpR → Cxt → Fma → Set where
    ax : {X : At} → just X ∣ [] ⊢R ` X
    Ir : nothing ∣ [] ⊢R I
    ⊗r : {S : StpR} → {Γ Δ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢R A → nothing ∣ Δ ⊢L B → S ∣ Γ ++ Δ ⊢R A ⊗ B 
    ⊗r[] : {Δ : Cxt}  {X : At} {A B : Fma} → 
              nothing ∣ [] ⊢R A → just X ∣ Δ ⊢R B → just X ∣ Δ ⊢R A ⊗ B 

subst-cxt : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢L A → S ∣ Γ' ⊢L A 
subst-cxt refl f = f

subst-cxtR : {S : StpR} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢R A → S ∣ Γ' ⊢R A 
subst-cxtR refl f = f

{- ================================================================ -}

-- admissibility of inverse of uf

uf-1' : {Γ Γ' : Cxt} → {A C : Fma}
  → nothing ∣ Γ' ⊢L C → Γ' ≡ A ∷ Γ
  → just A ∣ Γ ⊢L C
uf-1' (uf f) refl = f

uf-1 : {Γ : Cxt} → {A C : Fma}
  → nothing ∣ A ∷ Γ ⊢L C 
  → just A ∣ Γ ⊢L C
uf-1 f = uf-1' f refl

{- ================================================================ -}

-- admissibility of cut rules

mutual 
  scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
              S ∣ Γ ⊢L A  →  just A ∣ Δ' ⊢L C  →  S ∣ Γ ++ Δ' ⊢L C
  scut (Il f) g = Il (scut f g)
  scut (⊗l f) g = ⊗l (scut f g)
  scut (uf f) g = uf (scut f g)
  scut (switch-at f) g = scutR f g
  scut (switch-not f) g = scutR f g

  scutR : {S : StpR} → {Γ Δ' : Cxt} → {A C : Fma} → 
              S ∣ Γ ⊢R A  →  just A ∣ Δ' ⊢L C  →  mmap ` S ∣ Γ ++ Δ' ⊢L C
  scutR ax g = g
  scutR Ir (Il g) = g
  scutR (⊗r f f') (⊗l g) = scutR f (ccut [] f' g refl)
  scutR (⊗r[] f f') (⊗l g) = scutR f' (uf-1 (scutR f g))

  ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             nothing ∣ Γ ⊢L A  →  T ∣ Δ ⊢L C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢L C
  ccut Δ₀ f (Il g) r = Il (ccut Δ₀ f g r)
  ccut Δ₀ f (⊗l g) refl = ⊗l (ccut (_ ∷ Δ₀) f g refl)
  ccut Δ₀ f (uf g) r with cases∷ Δ₀ r
  ccut .[] f (uf g) r | inj₁ (refl , refl , refl) = scut f g
  ccut .(_ ∷ Δ₀) f (uf g) p | inj₂ (Δ₀ , r , refl) =  uf (ccut Δ₀ f g r)
  ccut Δ₀ f (switch-at g) r = switch-at (ccutR Δ₀ f g r)
  ccut Δ₀ f (switch-not g) r = ⊥-elim ([]disj∷ Δ₀ r)
  
  ccutR : {T : StpR} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             nothing ∣ Γ ⊢L A  →  T ∣ Δ ⊢R C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢R C
  ccutR Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccutR Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccutR Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
  ccutR Δ₀ f (⊗r g g') p | inj₁ (Γ₀ , refl , refl) = ⊗r (ccutR Δ₀ f g refl) g'
  ccutR ._ f (⊗r g g') p | inj₂ (Γ₀ , refl , refl) = ⊗r g (ccut Γ₀  f g' refl)
  ccutR Δ₀ f (⊗r[] g g') r = ⊗r[] g (ccutR Δ₀ f g' r)                                        

-- ====================================================================

-- admissible ⊗r and ⊗r[] rules with all premises in L-mode

mutual
  ⊗r[]L : {Δ : Cxt} → {A' A B : Fma}
    → nothing ∣ [] ⊢L A → just A' ∣ Δ ⊢L B
    → just A' ∣ Δ ⊢L A ⊗ B 
  ⊗r[]L f (Il g) = Il (⊗rL f g)
  ⊗r[]L f (⊗l g) = ⊗l (⊗r[]L f g)
  ⊗r[]L (switch-not f) (switch-at g) = switch-at (⊗r[] f g)
  
  ⊗rL : {S : Stp} → {Γ Δ : Cxt} → {A B : Fma}
    → S ∣ Γ ⊢L A → nothing ∣ Δ ⊢L B
    → S ∣ Γ ++ Δ ⊢L A ⊗ B
  ⊗rL (Il f) g = Il (⊗rL f g)
  ⊗rL (⊗l f) g = ⊗l (⊗rL f g)
  ⊗rL (uf f) g = uf (⊗rL f g)
  ⊗rL (switch-at f) g = switch-at (⊗r f g)
  ⊗rL (switch-not f) (uf g) = uf (⊗r[]L (switch-not f) g)
  ⊗rL (switch-not f) (switch-not g) = switch-not (⊗r f (switch-not g))

-- admissible ax in L-mode

axL : {A : Fma} → just A ∣ [] ⊢L A
axL {` X} = switch-at ax
axL {I} = Il (switch-not Ir)
axL {A ⊗ B} = ⊗l (⊗rL axL (uf axL))

-- ====================================================================

-- some provable equalities

⊗r[]ufL : {Γ : Cxt} → {A B C : Fma}
  → {f : nothing ∣ [] ⊢L B} {g : just A ∣ Γ ⊢L C}
  → ⊗rL f (uf g) ≡ uf (⊗r[]L f g)
⊗r[]ufL {f = switch-not f} = refl

⊗r[]uf-1L' : {Γ Γ' : Cxt} → {A B C : Fma}
  → (f : nothing ∣ [] ⊢L B)(g : nothing ∣ Γ' ⊢L C)
  → (r : Γ' ≡ A ∷ Γ)
  → ⊗r[]L f (uf-1' g r) ≡ uf-1' (⊗rL f g ) r
⊗r[]uf-1L' (switch-not f) (uf g) refl = refl

⊗ruf-1L' : {Γ Γ' Δ : Cxt} → {A B C : Fma}
  → (f : nothing ∣ Γ' ⊢L B) (g : nothing ∣ Δ ⊢L C)
  → (r : Γ' ≡ A ∷ Γ)
  → ⊗rL (uf-1' f r) g ≡ uf-1' (⊗rL f g ) (cong (λ x → x ++ Δ) r)
⊗ruf-1L' (uf f) g refl = refl

scut-uf-1' : {Γ Γ' Δ : Cxt} → {A A' C : Fma}
  → (f : nothing ∣ Γ' ⊢L A) (g : just A ∣ Δ ⊢L C) (r : Γ' ≡ A' ∷ Γ)
  → scut (uf-1' f r) g ≡ uf-1' (scut f g) (cong (λ z → z ++ Δ) r)
scut-uf-1' (uf f) g refl = refl

ccut-uf-1' : {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' C : Fma}
  → (f : nothing ∣ Γ ⊢L A) (g : nothing ∣ Δ ⊢L C) (r : Δ ≡ A' ∷ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f (uf-1' g r) refl ≡ uf-1' (ccut (A' ∷ Δ₀) f g r) refl
ccut-uf-1' Δ₀ f (uf g) refl = refl

abstract
  mutual
    ccut-⊗rL2 : {T : Stp} {Γ Δ Λ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A B C : Fma}
      → (f : nothing ∣ Γ ⊢L A) (g : T ∣ Λ ⊢L B) (g' : nothing ∣ Δ ⊢L C)
      → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
      → ccut (Λ ++ Δ₀) f (⊗rL g g') (cong (Λ ++_) r)
             ≡ ⊗rL g (ccut Δ₀ f g' r)
    ccut-⊗rL2 Δ₀ f (uf g) g' refl = cong uf (ccut-⊗rL2 Δ₀ f g g' refl)
    ccut-⊗rL2 Δ₀ f (Il g) g' r = cong Il (ccut-⊗rL2 Δ₀ f g g' r)
    ccut-⊗rL2 Δ₀ f (⊗l g) g' refl = cong ⊗l (ccut-⊗rL2 Δ₀ f g g' refl)
    ccut-⊗rL2 {Λ = Λ} Δ₀ {Δ'} {A} f (switch-at g) g' refl rewrite cases++-inj₂ Δ₀ Λ Δ' A = refl
    ccut-⊗rL2 Δ₀ f (switch-not g) (uf g') r with cases∷ Δ₀ r
    ccut-⊗rL2 .[] f (switch-not g) (uf g') refl | inj₁ (refl , refl , refl) =
      scut-⊗r[]L2-not f (switch-not g) g'
    ccut-⊗rL2 .(_ ∷ Γ₀) f (switch-not g) (uf g') refl | inj₂ (Γ₀ , refl , refl) =
      cong uf (ccut-⊗r[]L2 Γ₀ f (switch-not g) g' refl)
    ccut-⊗rL2 Δ₀ f (switch-not g) (switch-not g') r = ⊥-elim ([]disj∷ Δ₀ r)

    ccut-⊗r[]L2 : {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A A' B C : Fma}
      → (f : nothing ∣ Γ ⊢L A) (g : nothing ∣ [] ⊢L B) (g' : just A' ∣ Δ ⊢L C)
      → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
      → ccut Δ₀ f (⊗r[]L g g') r ≡ ⊗r[]L g (ccut Δ₀ f g' r)
    ccut-⊗r[]L2 Δ₀ f g (Il g') refl = cong Il (ccut-⊗rL2 Δ₀ f g g' refl)
    ccut-⊗r[]L2 Δ₀ f g (⊗l g') refl = cong ⊗l (ccut-⊗r[]L2 (_ ∷ Δ₀) f g g' refl)
    ccut-⊗r[]L2 Δ₀ f (switch-not g) (switch-at g') r = refl

    scut-⊗r[]L2-not : {Γ Δ : Cxt} → {A B C : Fma}
      → (f : nothing ∣ Γ ⊢L A) (g : nothing ∣ [] ⊢L B)  (g' : just A ∣ Δ ⊢L C)
      →  scut f (⊗r[]L g g') ≡ ⊗rL g (scut f g')
    scut-⊗r[]L2-not (uf f) (switch-not g) g' = cong uf (scut-⊗r[]L2-fma f (switch-not g) g')
    scut-⊗r[]L2-not (switch-not f) (switch-not g) g' = scutR-⊗r[]L2-not f (switch-not g) g'

    scutR-⊗r[]L2-not : {Γ Δ : Cxt} → {A B C : Fma}
      → (f : nothing ∣ Γ ⊢R A) (g : nothing ∣ [] ⊢L B)  (g' : just A ∣ Δ ⊢L C)
      →  scutR f (⊗r[]L g g') ≡ ⊗rL g (scutR f g')
    scutR-⊗r[]L2-not Ir (switch-not f) (Il g') = refl
    scutR-⊗r[]L2-not (⊗r f f') g (⊗l g') =
      trans
        (cong (scutR f) (ccut-⊗r[]L2 [] f' g g' refl))
        (scutR-⊗r[]L2-not f g (ccut [] f' g' refl))
    
    scut-⊗r[]L2-fma : {Γ Δ : Cxt} → {A A' B C : Fma}
      → (f : just A' ∣ Γ ⊢L A) (g : nothing ∣ [] ⊢L B)  (g' : just A ∣ Δ ⊢L C)
      →  scut f (⊗r[]L g g') ≡ ⊗r[]L g (scut f g')
    scut-⊗r[]L2-fma (Il f) g g' = cong Il (scut-⊗r[]L2-not f g g')
    scut-⊗r[]L2-fma (⊗l f) g g' = cong ⊗l (scut-⊗r[]L2-fma f g g')
    scut-⊗r[]L2-fma (switch-at f) (switch-not g) g' = scutR-⊗r[]L2-fma f (switch-not g) g'

    scutR-⊗r[]L2-fma : {Γ Δ : Cxt} → {X : At} {A B C : Fma}
      → (f : just X ∣ Γ ⊢R A) (g : nothing ∣ [] ⊢L B)  (g' : just A ∣ Δ ⊢L C)
      →  scutR f (⊗r[]L g g') ≡ ⊗r[]L g (scutR f g')
    scutR-⊗r[]L2-fma ax g g' = refl
    scutR-⊗r[]L2-fma (⊗r f f') g (⊗l g') =
      trans
        (cong (scutR f) (ccut-⊗r[]L2 [] f' g g' refl))
        (scutR-⊗r[]L2-fma f g _)
    scutR-⊗r[]L2-fma (⊗r[] f f') (switch-not g) (⊗l g') =
      trans
        (cong (scutR f')
          (trans
            (cong uf-1 (scutR-⊗r[]L2-not f (switch-not g) g'))
            (sym (⊗r[]uf-1L' (switch-not g) (scutR f g') refl))))
        (scutR-⊗r[]L2-fma f' (switch-not g) _)

  mutual
    ccut-⊗rL1 : {T : Stp} {Γ Δ Λ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A B C : Fma}
      → (f : nothing ∣ Γ ⊢L A) (g : T ∣ Δ ⊢L B) (g' : nothing ∣ Λ ⊢L C)
      → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
      → ccut Δ₀ {Δ' ++ Λ} f (⊗rL g g') (cong (_++ Λ) {Δ}{Δ₀ ++ A ∷ Δ'} r)
             ≡ ⊗rL (ccut Δ₀ f g r) g'
    ccut-⊗rL1 Δ₀ f (uf g) g' r with cases∷ Δ₀ r
    ccut-⊗rL1 .[] f (uf g) g' refl | inj₁ (refl , refl , refl) =
      scut-⊗rL2 f g g'
    ccut-⊗rL1 .(_ ∷ Γ₀) f (uf g) g' refl | inj₂ (Γ₀ , refl , refl) =
      cong uf (ccut-⊗rL1 Γ₀ f g g' refl)
    ccut-⊗rL1 Δ₀ f (Il g) g' r =
      cong Il (ccut-⊗rL1 Δ₀ f g g' r)
    ccut-⊗rL1 Δ₀ f (⊗l g) g' refl =
      cong ⊗l (ccut-⊗rL1 (_ ∷ Δ₀) f g g' refl)
    ccut-⊗rL1 {Λ = Λ} Δ₀ {Δ'} {A} f (switch-at g) g' refl rewrite cases++-inj₁ Δ₀ Δ' Λ A = refl
    ccut-⊗rL1 {Λ = Λ} Δ₀ {Δ'} {A} f (switch-not g) g' r = ⊥-elim ([]disj∷ Δ₀ r)

    scut-⊗rL2 : {S : Stp} {Γ Δ Δ' : Cxt} → {A B C : Fma}
      → (f : S ∣ Γ ⊢L A) (g : just A ∣ Δ ⊢L B)  (g' : nothing ∣ Δ' ⊢L C)
      →  scut f (⊗rL g g') ≡ ⊗rL (scut f g) g'
    scut-⊗rL2 (uf f) g g' = cong uf (scut-⊗rL2 f g g')
    scut-⊗rL2 (Il f) g g' = cong Il (scut-⊗rL2 f g g')
    scut-⊗rL2 (⊗l f) g g' = cong ⊗l (scut-⊗rL2 f g g')
    scut-⊗rL2 (switch-at f) g g' = scutR-⊗rL2 f g g'
    scut-⊗rL2 (switch-not f) g g' = scutR-⊗rL2 f g g'
    
    scutR-⊗rL2 : {S : StpR} {Γ Δ Δ' : Cxt} → {A B C : Fma}
      → (f : S ∣ Γ ⊢R A) (g : just A ∣ Δ ⊢L B)  (g' : nothing ∣ Δ' ⊢L C)
      →  scutR f (⊗rL g g') ≡ ⊗rL (scutR f g) g'
    scutR-⊗rL2 ax g g' = refl
    scutR-⊗rL2 Ir (Il g) g' = refl
    scutR-⊗rL2 (⊗r f f') (⊗l g) g' = 
      trans (cong (scutR f) (ccut-⊗rL1 [] f' g g' refl))
        (scutR-⊗rL2 f (ccut [] f' g refl) g')
    scutR-⊗rL2 (⊗r[] f f') (⊗l g) g' =
      trans
        (cong (scutR f')
          (trans
            (cong uf-1 (scutR-⊗rL2 f g g'))
            (sym (⊗ruf-1L' (scutR f g) g' refl))))
        (scutR-⊗rL2 f' (uf-1 (scutR f g)) g')

{- ================================================================ -}

-- Inverse rules of Il and ⊗l

Il-1 : {Γ : Cxt} → {C : Fma} → 
              just I ∣ Γ ⊢L C → nothing ∣ Γ ⊢L C
Il-1 (Il f) = f

⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
            just (A ⊗ B) ∣ Γ ⊢L C → just A ∣ B ∷ Γ ⊢L C
⊗l-1 (⊗l f) = f

IlIl-1 : {Γ : Cxt} → {C : Fma} → 
              (f : just I ∣ Γ ⊢L C) → Il (Il-1 f) ≡ f
IlIl-1 (Il f) = refl

⊗l⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
            (f : just (A ⊗ B) ∣ Γ ⊢L C) → ⊗l (⊗l-1 f) ≡ f
⊗l⊗l-1 (⊗l f) = refl

-- Interaction of cut rules with Il-1 and ⊗l-1

scut⊗l-1 : {Γ Δ : Cxt} → {A B C D : Fma}
  → (f : just (A ⊗ B) ∣ Γ ⊢L C)(g : just C ∣ Δ ⊢L D)
  → ⊗l-1 (scut f g) ≡ scut (⊗l-1 f) g
scut⊗l-1 (⊗l f) g = refl

scutIl-1 : {Γ Δ : Cxt} → {A C : Fma}
  → (f : just I ∣ Γ ⊢L A)(g : just A ∣ Δ ⊢L C)
  → Il-1 (scut f g) ≡ scut (Il-1 f) g
scutIl-1 (Il f) g = refl

scutR-Ir : {Γ : Cxt} → {C : Fma}
  → (f : just I ∣ Γ ⊢L C)
  → scutR Ir f ≡ Il-1 f
scutR-Ir (Il f) = refl

-- ===================================================
-- ===================================================

-- Cut-free unfocused sequent calculus for left-normal skew monoidal
-- categories

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  uf : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢ C → nothing ∣ A ∷ Γ ⊢ C
  Ir : nothing ∣ [] ⊢ I
  ⊗r : {S : Stp} → {Γ Δ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ A → nothing ∣ Δ ⊢ B → S ∣ Γ ++ Δ ⊢ A ⊗ B 
  Il : {Γ : Cxt} → {C : Fma} → 
              nothing ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ B ∷ Γ ⊢ C → just (A ⊗ B) ∣ Γ ⊢ C
  ⊗r[] : {Γ : Cxt} → {A B C : Fma} → 
              nothing ∣ [] ⊢ B → just A ∣ Γ ⊢ C →
              just A ∣ Γ ⊢ B ⊗ C

-- equality of derivations

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h
  uf : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≗ g → uf f ≗ uf g
  ⊗l : ∀{Γ}{A}{B}{C}{f g : just A ∣ B ∷ Γ ⊢ C} → f ≗ g → ⊗l f ≗ ⊗l g
  Il : ∀{Γ}{C}{f g : nothing ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊗r : ∀{S}{Γ}{Δ}{A}{B}{f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
    → f ≗ g → f' ≗ g' → ⊗r f f' ≗ ⊗r g g'
  ⊗r[] : ∀{Δ}{A'}{A}{B}{f g : nothing ∣ [] ⊢ A}{f' g' : just A' ∣ Δ ⊢ B}
    → f ≗ g → f' ≗ g' → ⊗r[] f f' ≗ ⊗r[] g g'
  axI : ax ≗ Il Ir
  ax⊗ : {A B : Fma} → ax {A ⊗ B} ≗ ⊗l (⊗r ax (uf ax))
  ⊗ruf : {Γ Δ : Cxt}{A' A B : Fma}
    → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (uf f) g ≗ uf (⊗r f g)
  ⊗rIl : {Γ Δ : Cxt}{A B : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (Il f) g ≗ Il (⊗r f g)
  ⊗r⊗l : {Γ Δ : Cxt}{A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗l f) g ≗ ⊗l (⊗r f g)
  ⊗r[]uf : {Γ : Cxt} → {A B C : Fma}
    → {f : nothing ∣ [] ⊢ B} {g : just A ∣ Γ ⊢ C}
    → ⊗r f (uf g) ≗ uf (⊗r[] f g)
  ⊗r[]Il : {Γ : Cxt} → {A B : Fma}
    → {f : nothing ∣ [] ⊢ A} {g : nothing ∣ Γ ⊢ B}
    → ⊗r[] f (Il g) ≗ Il (⊗r f g)
  ⊗r[]⊗l : {Γ : Cxt} → {A' B' A B : Fma}
    → {f : nothing ∣ [] ⊢ A} {g : just A' ∣ B' ∷ Γ ⊢ B}
    → ⊗r[] f (⊗l g) ≗ ⊗l (⊗r[] f g)

-- Embedding of focused derivation in the unfocused sequent calculus

mutual 
  embL : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢L C → S ∣ Γ ⊢ C
  embL (Il f) = Il (embL f)
  embL (⊗l f) = ⊗l (embL f)
  embL (uf f) = uf (embL f)
  embL (switch-at f) = embR f
  embL (switch-not f) = embR f

  embR : {S : StpR} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢R C → mmap ` S ∣ Γ ⊢ C
  embR ax = ax
  embR Ir = Ir
  embR (⊗r f g) = ⊗r (embR f) (embL g)
  embR (⊗r[] f g) = ⊗r[] (embR f) (embR g)

-- Focusing function

focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢ C → S ∣ Γ  ⊢L C
focus ax = axL
focus (uf f) = uf (focus f) 
focus Ir = switch-not Ir
focus (⊗r f g) = ⊗rL (focus f) (focus g)
focus (Il f) = Il (focus f)
focus (⊗l f) = ⊗l (focus f)
focus (⊗r[] f g) = ⊗r[]L (focus f) (focus g)

-- Focusing is compatible with ≗ 

focus-compat : {S : Stp} → {Γ : Cxt} → {C : Fma}
  → {f g : S ∣ Γ ⊢ C} → f ≗ g → focus f ≡ focus g
focus-compat refl = refl
focus-compat (~ p) = sym (focus-compat p)
focus-compat (p ∙ p₁) = trans (focus-compat p) (focus-compat p₁)
focus-compat (uf p) = cong uf (focus-compat p)
focus-compat (⊗l p) = cong ⊗l (focus-compat p)
focus-compat (Il p) = cong Il (focus-compat p)
focus-compat (⊗r p p₁) = cong₂ ⊗rL (focus-compat p) (focus-compat p₁)
focus-compat (⊗r[] p p₁) = cong₂ ⊗r[]L (focus-compat p) (focus-compat p₁)
focus-compat axI = refl
focus-compat ax⊗ = refl
focus-compat ⊗ruf = refl
focus-compat ⊗rIl = refl
focus-compat ⊗r⊗l = refl
focus-compat ⊗r[]uf = ⊗r[]ufL
focus-compat ⊗r[]Il = refl
focus-compat ⊗r[]⊗l = refl

-- focus (embL f) ≡ f

focus-embR-not : {C : Fma} {Γ : Cxt}
  → (f : nothing ∣ Γ ⊢R C) (eq : Γ ≡ [])
  → focus (embR f) ≡ subst-cxt (sym eq) (switch-not (subst-cxtR eq f))
focus-embR-not Ir refl = refl
focus-embR-not (⊗r {Γ = []} f (switch-not g)) refl =
  cong₂ ⊗rL (focus-embR-not f refl) (focus-embR-not g refl)

mutual
  focus-embL : {S : Stp} → {Γ : Cxt} → {C : Fma}
    → (f : S ∣ Γ ⊢L C)
    → focus (embL f) ≡ f
  focus-embL (Il f) = cong Il (focus-embL f)
  focus-embL (⊗l f) = cong ⊗l (focus-embL f)
  focus-embL (uf f) = cong uf (focus-embL f)
  focus-embL (switch-at f) = focus-embR-at f
  focus-embL (switch-not f) = focus-embR-not f refl

  focus-embR-at : {X : At} → {Γ : Cxt} → {C : Fma}
    → (f : just X ∣ Γ ⊢R C)
    → focus (embR f) ≡ switch-at f
  focus-embR-at ax = refl
  focus-embR-at (⊗r f g) = cong₂ ⊗rL (focus-embR-at f) (focus-embL g)  
  focus-embR-at (⊗r[] f g) =
    cong₂ ⊗r[]L (focus-embR-not f refl) (focus-embR-at g) 

-- embL (focus f) ≗ f

mutual
  embL-⊗r[]L : {Δ : Cxt} → {A' A B : Fma} → 
                (f₁ : nothing ∣ [] ⊢L A)  → (f₂ : just A' ∣ Δ ⊢L B) → 
                embL (⊗r[]L f₁ f₂) ≗ ⊗r[] (embL f₁) (embL f₂)
  embL-⊗r[]L f (Il g) = Il (embL-⊗rL f g) ∙ ~ ⊗r[]Il
  embL-⊗r[]L f (⊗l g) = ⊗l (embL-⊗r[]L f g) ∙ ~ ⊗r[]⊗l
  embL-⊗r[]L (switch-not f) (switch-at g) = refl
  
  embL-⊗rL : {S : Stp} → {Γ Δ : Cxt} → {A B : Fma} → 
                (f₁ : S ∣ Γ ⊢L A)  → (f₂ : nothing ∣ Δ ⊢L B) → 
                embL (⊗rL f₁ f₂) ≗ ⊗r (embL f₁) (embL f₂)
  embL-⊗rL (uf f₁) f₂ = 
    uf (embL-⊗rL f₁ f₂) ∙ (~ ⊗ruf)
  embL-⊗rL (Il f₁) f₂ =
    Il (embL-⊗rL f₁ f₂) ∙ ~ ⊗rIl
  embL-⊗rL (⊗l f₁) f₂ =
    ⊗l (embL-⊗rL f₁ f₂) ∙ (~ ⊗r⊗l) 
  embL-⊗rL (switch-at f₁) f₂ = refl
  embL-⊗rL (switch-not f₁) (uf f₂) =
    uf (embL-⊗r[]L (switch-not f₁) f₂) ∙ ~ ⊗r[]uf
  embL-⊗rL (switch-not f₁) (switch-not f) = refl

embL-axL : {A : Fma} → embL (axL {A}) ≗ ax
embL-axL {` X} = refl
embL-axL {I} = ~ axI
embL-axL {A₁ ⊗ A₂} =
  ⊗l (embL-⊗rL axL (uf axL) ∙ ⊗r embL-axL (uf embL-axL))
  ∙ ~ ax⊗

embL-focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
             (f : S ∣ Γ ⊢ C)  → embL (focus f) ≗ f
embL-focus ax = embL-axL
embL-focus (uf f) = uf (embL-focus f)
embL-focus Ir = refl
embL-focus (⊗r f f₁) =
  embL-⊗rL (focus f) (focus f₁)
  ∙ ⊗r (embL-focus f) (embL-focus f₁)
embL-focus (Il f) = Il (embL-focus f)
embL-focus (⊗l f) = ⊗l (embL-focus f)
embL-focus (⊗r[] f f₁) =
  embL-⊗r[]L (focus f) (focus f₁)
  ∙ ⊗r[] (embL-focus f) (embL-focus f₁)

-- =======================================================================

-- A stoup free focused calculus, and a proof that it is equivalent to
-- the focused calculus with stoup.

infix 3 _⊢L_ _⊢R_

mutual
  data _⊢L_ : Cxt → Fma → Set where
    Il : {Γ : Cxt} → {C : Fma} → 
              Γ ⊢L C → I ∷ Γ ⊢L C 
    ⊗l : {Γ : Cxt} → {A B C : Fma} → 
              A ∷ B ∷ Γ ⊢L C → A ⊗ B ∷ Γ ⊢L C
    switch-at :  {X : At} {Γ : Cxt} {C : Fma} → 
              (f : ` X ∷ Γ ⊢R C) → ` X ∷ Γ ⊢L C
    switch-not :  {C : Fma} → 
              (f : [] ⊢R C) → [] ⊢L C

  data _⊢R_ : Cxt → Fma → Set where
    ax : {X : At} → ` X ∷ [] ⊢R ` X
    Ir : [] ⊢R I
    ⊗r : {Γ Δ : Cxt} → {A B : Fma} → 
              Γ ⊢R A → Δ ⊢L B → Γ ++ Δ ⊢R A ⊗ B 

subst-cxtL' : {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → Γ ⊢L A → Γ' ⊢L A 
subst-cxtL' refl f = f

subst-cxtR' : {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → Γ ⊢R A → Γ' ⊢R A 
subst-cxtR' refl f = f

mutual
  ⊗r[]L' : {Δ : Cxt} → {A B : Fma} → 
         [] ⊢L A → Δ ⊢L B → Δ ⊢L A ⊗ B 
  ⊗r[]L' f (Il g) = Il (⊗rL' f g)
  ⊗r[]L' f (⊗l g) = ⊗l (⊗r[]L' f g)
  ⊗r[]L' (switch-not f) (switch-at f₁) = switch-at (⊗r f (switch-at f₁))
  ⊗r[]L' (switch-not f) (switch-not f₁) = switch-not (⊗r f (switch-not f₁))
  
  ⊗rL' : {Γ Δ : Cxt} → {A B : Fma} → 
         Γ ⊢L A → Δ ⊢L B → Γ ++ Δ ⊢L A ⊗ B 
  ⊗rL' (Il f) g = Il (⊗rL' f g)
  ⊗rL' (⊗l f) g = ⊗l (⊗rL' f g)
  ⊗rL' (switch-at f) g = switch-at (⊗r f g)
  ⊗rL' (switch-not f) g = ⊗r[]L' (switch-not f) g

⊗r[]L'-at : {Δ Δ' : Cxt} {X : At} {A B : Fma} → 
         (f : [] ⊢R A) (g : Δ' ⊢L B) (eq : Δ' ≡ ` X ∷ Δ) →
         ⊗r[]L' (switch-not f) g
         ≡ subst-cxtL' (sym eq) (switch-at (subst-cxtR' eq (⊗r f g)))
⊗r[]L'-at f (switch-at f₁) refl = refl

⊗r[]L'-not : {A B : Fma} → 
         (f : [] ⊢R A) (g : [] ⊢L B) → 
         ⊗r[]L' (switch-not f) g
         ≡ switch-not (⊗r f g)
⊗r[]L'-not f (switch-not f₁) = refl

mutual
  stp→nostpL-j : {Γ : Cxt} {A C : Fma}
    → just A ∣ Γ ⊢L C → A ∷ Γ ⊢L C
  stp→nostpL-j (Il f) = Il (stp→nostpL-n f)
  stp→nostpL-j (⊗l f) = ⊗l (stp→nostpL-j f)
  stp→nostpL-j (switch-at f) = switch-at (stp→nostpR-j f)

  stp→nostpL-n : {Γ : Cxt} {C : Fma}
    → nothing ∣ Γ ⊢L C → Γ ⊢L C
  stp→nostpL-n (uf f) = stp→nostpL-j f
  stp→nostpL-n (switch-not f) = switch-not (stp→nostpR-n f)

  stp→nostpR-j : {Γ : Cxt} {X : At} {C : Fma}
    → just X ∣ Γ ⊢R C → ` X ∷ Γ ⊢R C
  stp→nostpR-j ax = ax
  stp→nostpR-j (⊗r f g) = ⊗r (stp→nostpR-j f) (stp→nostpL-n g)
  stp→nostpR-j (⊗r[] f g) = ⊗r (stp→nostpR-n f) (switch-at (stp→nostpR-j g))
  
  stp→nostpR-n : {Γ : Cxt} {C : Fma}
    → nothing ∣ Γ ⊢R C → Γ ⊢R C
  stp→nostpR-n Ir = Ir
  stp→nostpR-n (⊗r f g) = ⊗r (stp→nostpR-n f) (stp→nostpL-n g)

uf-1L : {Γ Γ' : Cxt} {A C : Fma}
  → nothing ∣ Γ' ⊢L C → Γ' ≡ A ∷ Γ → just A ∣ Γ ⊢L C
uf-1L (uf f) refl = f

mutual
  nostp→stpL : {Γ : Cxt} {C : Fma} → Γ ⊢L C → nothing ∣ Γ ⊢L C
  nostp→stpL (Il f) = uf (Il (nostp→stpL f))
  nostp→stpL (⊗l f) = uf (⊗l (uf-1L (nostp→stpL f) refl))
  nostp→stpL (switch-at f) = nostp→stpR f
  nostp→stpL (switch-not f) = nostp→stpR f

  nostp→stpR : {Γ : Cxt} {C : Fma}
    → Γ ⊢R C → nothing ∣ Γ ⊢L C
  nostp→stpR ax = uf (switch-at ax)
  nostp→stpR Ir = switch-not Ir
  nostp→stpR (⊗r f g) = ⊗rL (nostp→stpR f) (nostp→stpL g)

nostp→stpL-j-uf-1 : {Γ Γ' : Cxt} {A C : Fma}
  → (f : nothing ∣ Γ' ⊢L C) (eq : Γ' ≡ A ∷ Γ)
  → stp→nostpL-j (uf-1L f eq) ≡ subst-cxtL' eq (stp→nostpL-n f) 
nostp→stpL-j-uf-1 (uf f) refl = refl

mutual
  stp→nostpL-n-⊗rL : {Γ Δ : Cxt} {A B : Fma}
    → (f : nothing ∣ Γ ⊢L A) (g : nothing ∣ Δ ⊢L B)
    → stp→nostpL-n (⊗rL f g) ≡ ⊗rL' (stp→nostpL-n f) (stp→nostpL-n g)
  stp→nostpL-n-⊗rL (uf f) g = stp→nostpL-j-⊗rL f g
  stp→nostpL-n-⊗rL (switch-not f) (uf g) = stp→nostpL-j-⊗r[]L (switch-not f) g
  stp→nostpL-n-⊗rL (switch-not f) (switch-not g) = refl

  stp→nostpL-j-⊗r[]L : {Γ : Cxt} {A' A B : Fma}
    → (f : nothing ∣ [] ⊢L A) (g : just A' ∣ Γ ⊢L B)
    → stp→nostpL-j (⊗r[]L f g)
      ≡ ⊗r[]L' (stp→nostpL-n f) (stp→nostpL-j g)
  stp→nostpL-j-⊗r[]L f (Il g) = cong Il (stp→nostpL-n-⊗rL f g)
  stp→nostpL-j-⊗r[]L f (⊗l g) = cong ⊗l (stp→nostpL-j-⊗r[]L f g)
  stp→nostpL-j-⊗r[]L (switch-not f) (switch-at g) = refl

  stp→nostpL-j-⊗rL : {Γ Δ : Cxt} {A' A B : Fma}
    → (f : just A' ∣ Γ ⊢L A) (g : nothing ∣ Δ ⊢L B)
    → stp→nostpL-j (⊗rL f g) ≡ ⊗rL' (stp→nostpL-j f) (stp→nostpL-n g)
  stp→nostpL-j-⊗rL (Il f) g = cong Il (stp→nostpL-n-⊗rL f g)
  stp→nostpL-j-⊗rL (⊗l f) g = cong ⊗l (stp→nostpL-j-⊗rL f g)
  stp→nostpL-j-⊗rL (switch-at f) g = refl
  
mutual
  iso1-pt1 : {Γ : Cxt} {C : Fma} (f : Γ ⊢L C)
    → stp→nostpL-n (nostp→stpL f) ≡ f
  iso1-pt1 (Il f) = cong Il (iso1-pt1 f)
  iso1-pt1 (⊗l f) = cong ⊗l
    (trans (nostp→stpL-j-uf-1 (nostp→stpL f) refl)
      (iso1-pt1 f))
  iso1-pt1 (switch-at f) = iso1-pt1R-j f refl
  iso1-pt1 (switch-not f) = iso1-pt1R-n f refl
  
  iso1-pt1R-j : {Γ Γ' : Cxt} {X : At} {C : Fma}
    → (f : Γ' ⊢R C) (eq : Γ' ≡ ` X ∷ Γ)
    → stp→nostpL-n (nostp→stpR f) ≡
      subst-cxtL' (sym eq) (switch-at (subst-cxtR' eq f))
  iso1-pt1R-j ax refl = refl
  iso1-pt1R-j (⊗r {[]} f g) refl =
    trans (stp→nostpL-n-⊗rL (nostp→stpR f) (nostp→stpL g))
      (trans (cong₂ ⊗rL' (iso1-pt1R-n f refl) (iso1-pt1 g))
        (⊗r[]L'-at f g refl))
  iso1-pt1R-j (⊗r {.(` _) ∷ Γ} f g) refl =
    trans (stp→nostpL-n-⊗rL (nostp→stpR f) (nostp→stpL g))
      (cong₂ ⊗rL' (iso1-pt1R-j f refl) (iso1-pt1 g))

  iso1-pt1R-n : {Γ : Cxt} {C : Fma}
    → (f : Γ ⊢R C) (eq : Γ ≡ [])
    → stp→nostpL-n (nostp→stpR f) ≡ 
      subst-cxtL' (sym eq) (switch-not (subst-cxtR' eq f))
  iso1-pt1R-n Ir refl = refl
  iso1-pt1R-n (⊗r {[]} f g) refl =
    trans (stp→nostpL-n-⊗rL (nostp→stpR f) (nostp→stpL g))
      (trans (cong₂ ⊗rL' (iso1-pt1R-n f refl) (iso1-pt1 g))
        (⊗r[]L'-not f g))

mutual
  iso1-pt2-n : {Γ : Cxt} {C : Fma} (f : nothing ∣ Γ ⊢L C)
    → nostp→stpL (stp→nostpL-n f) ≡ f
  iso1-pt2-n (uf f) = iso1-pt2-j f
  iso1-pt2-n (switch-not f) = iso1-pt2R-n f refl

  iso1-pt2-j : {Γ : Cxt} {A C : Fma} (f : just A ∣ Γ ⊢L C)
    → nostp→stpL (stp→nostpL-j f) ≡ uf f
  iso1-pt2-j (Il f) = cong uf (cong Il (iso1-pt2-n f))
  iso1-pt2-j (⊗l f) =
    cong uf (cong ⊗l (cong (λ x → uf-1L x refl) (iso1-pt2-j f)))
  iso1-pt2-j (switch-at f) = iso1-pt2R-j f
  
  iso1-pt2R-n : {Γ : Cxt} {C : Fma} (f : nothing ∣ Γ ⊢R C) (eq : Γ ≡ [])
    → nostp→stpR (stp→nostpR-n f)
      ≡ subst-cxt (sym eq) (switch-not (subst-cxtR eq f))
  iso1-pt2R-n Ir refl = refl
  iso1-pt2R-n (⊗r {Γ = []} f (switch-not g)) refl =
    cong₂ ⊗rL (iso1-pt2R-n f refl) (iso1-pt2R-n g refl)
  
  iso1-pt2R-j : {Γ : Cxt} {X : At} {C : Fma} (f : just X ∣ Γ ⊢R C)
    → nostp→stpR (stp→nostpR-j f) ≡ uf (switch-at f)
  iso1-pt2R-j ax = refl
  iso1-pt2R-j (⊗r f g) = cong₂ ⊗rL (iso1-pt2R-j f) (iso1-pt2-n g)
  iso1-pt2R-j (⊗r[] f g) = cong₂ ⊗rL (iso1-pt2R-n f refl) (iso1-pt2R-j g)
