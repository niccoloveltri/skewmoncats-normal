{-# OPTIONS --rewriting #-}

module SeqCalc where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Fsk

-- =======================================================================

-- Sequent calculus for associative-normal skew monoidal categories

Stp : Set
Stp = Maybe Fma

Cxt : Set
Cxt = List Fma

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
  ⊗c : {S : Stp} → (Γ Δ : Cxt) → {J J' C : Fma} → 
              S ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C → S ∣ Γ ++ J ⊗ J' ∷ Δ ⊢ C 

subst-cxt : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subst-cxt refl f = f

-- ====================================================================
  
-- An interpretation of antecedents as contexts 

asCxt : Bool → Stp → Cxt → Cxt
asCxt b (just A) Γ = A ∷ Γ
asCxt false nothing Γ = Γ
asCxt true nothing Γ = I ∷ Γ

asCxt++ : (b : Bool) (S : Stp)(Γ Δ : Cxt)
  → asCxt b S (Γ ++ Δ) ≡ asCxt b S Γ ++ Δ
asCxt++ b (just S) Γ Δ = refl  
asCxt++ false nothing Γ Δ = refl
asCxt++ true nothing Γ Δ = refl

{-# REWRITE asCxt++ #-}



-- inverted left rules

Il-1 : {Γ : Cxt} → {C : Fma} → 
              just I ∣ Γ ⊢ C → nothing ∣ Γ ⊢ C
Il-1 ax = Ir
Il-1 (⊗r f f₁) = ⊗r (Il-1 f) f₁
Il-1 (Il f) = f
Il-1 (⊗c Γ Δ f) = ⊗c Γ Δ (Il-1 f)              

⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
            just (A ⊗ B) ∣ Γ ⊢ C → just A ∣ B ∷ Γ ⊢ C
⊗l-1 ax = ⊗r ax (uf ax)
⊗l-1 (⊗r f f₁) = ⊗r (⊗l-1 f) f₁
⊗l-1 (⊗l f) = f
⊗l-1 (⊗c Γ Δ f) = ⊗c (_ ∷ Γ) Δ (⊗l-1 f)              


-- ====================================================================

-- -- equality of proofs 

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h
  uf : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≗ g → uf f ≗ uf g
  ⊗l : ∀{Γ}{A}{B}{C}{f g : just A ∣ B ∷ Γ ⊢ C} → f ≗ g → ⊗l f ≗ ⊗l g
  Il : ∀{Γ}{C}{f g : nothing ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊗r : ∀{S}{Γ}{Δ}{A}{B}{f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
    → f ≗ g → f' ≗ g' → ⊗r f f' ≗ ⊗r g g'
  axI : ax ≗ Il Ir
  ax⊗ : {A B : Fma} → ax {A ⊗ B} ≗ ⊗l (⊗r ax (uf ax))
  ⊗ruf : {Γ Δ : Cxt}{A A' B : Fma}
    → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (uf f) g ≗ uf (⊗r f g)
  ⊗rIl : {Γ Δ : Cxt}{A B : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (Il f) g ≗ Il (⊗r f g)
  ⊗r⊗l : {Γ Δ : Cxt}{A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗l f) g ≗ ⊗l (⊗r f g)

  ⊗c : ∀{S} Γ Δ {C J J'} 
    → {f g : S ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C}
    → f ≗ g → ⊗c Γ Δ f ≗ ⊗c Γ Δ g
  uf⊗c1 : {Γ : Cxt} {C J J' : Fma} 
    → {f : just J ∣ J' ∷ Γ ⊢ C}
    → uf (⊗l f) ≗ ⊗c [] Γ (uf f)
  ⊗c⊗c : {S : Stp} {Γ Δ Λ : Cxt} {C J J' K K' : Fma}
    → {f : S ∣ Γ ++ J ∷ J' ∷ Δ ++ K ∷ K' ∷ Λ ⊢ C}
    → ⊗c Γ (Δ ++ K ⊗ K' ∷ Λ) (⊗c (Γ ++ J ∷ J' ∷ Δ) Λ f)
          ≗ ⊗c (Γ ++ J ⊗ J' ∷ Δ) Λ (⊗c Γ (Δ ++ K ∷ K' ∷ Λ) f)
  uf⊗c2 : {Γ Δ : Cxt} {A C J J' : Fma}
    → {f : just A ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C}
    → uf (⊗c Γ Δ f) ≗ ⊗c (A ∷ Γ) Δ (uf f)
  Il⊗c : {Γ Δ : Cxt} {C J J' : Fma}
    → {f : nothing ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C}
    → Il (⊗c Γ Δ f) ≗ ⊗c Γ Δ (Il f)
  ⊗l⊗c : {Γ Δ : Cxt} {A B C J J' : Fma}
    → {f : just A ∣ B ∷ Γ ++ J ∷ J' ∷ Δ ⊢ C}
    → ⊗l (⊗c (B ∷ Γ) Δ f) ≗ ⊗c Γ Δ (⊗l f)
  ⊗r⊗c1 : {S : Stp}{Γ Γ' Δ : Cxt}{A B J J' : Fma}
    → {f : S ∣ Γ ++ J ∷ J' ∷ Γ' ⊢ A} {g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗c Γ Γ' f) g ≗ ⊗c Γ (Γ' ++ Δ) (⊗r f g)
  ⊗r⊗c2 : {S : Stp}{Γ Δ Δ' : Cxt}{A B J J' : Fma}
    → {f : S ∣ Γ ⊢ A} {g : nothing ∣ Δ ++ J ∷ J' ∷ Δ' ⊢ B}
    → ⊗r f (⊗c Δ Δ' g) ≗ ⊗c (Γ ++ Δ) Δ' (⊗r f g)

≡-to-≗ : ∀{S}{Γ}{A}{f f' : S ∣ Γ ⊢ A} → f ≡ f' → f ≗ f'
≡-to-≗ refl = refl

-- -- equational reasoning sugar for ≗

infix 4 _≗'_
infix 1 proof≗_
infixr 2 _≗〈_〉_
infix 3 _qed≗

data _≗'_ {S  : Stp}{Γ : Cxt}{A : Fma} (f g : S ∣ Γ ⊢ A) : Set where
  relto :  f ≗ g → f ≗' g

proof≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} {f g : S ∣ Γ ⊢ A} → f ≗' g → f ≗ g
proof≗ relto p = p

_≗〈_〉_ :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) {g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗' h → f ≗' h 

_ ≗〈 p 〉 relto q = relto (p ∙ q)

_qed≗  :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) → f ≗' f
_qed≗ _ = relto refl


-- ====================================================================

-- -- compatibility of inverse left rules with ≗

abstract
  congIl-1 : {Γ : Cxt} → {C : Fma} → 
                {f g : just I ∣ Γ ⊢ C} →
                f ≗ g → Il-1 f ≗ Il-1 g
  congIl-1 refl = refl
  congIl-1 (~ p) = ~ congIl-1 p
  congIl-1 (p ∙ p₁) = congIl-1 p ∙ congIl-1 p₁
  congIl-1 (Il p) = p
  congIl-1 (⊗r p p₁) = ⊗r (congIl-1 p) p₁
  congIl-1 axI = refl
  congIl-1 ⊗rIl = refl
  congIl-1 (⊗c Γ Δ p) = ⊗c Γ Δ (congIl-1 p)
  congIl-1 ⊗c⊗c = ⊗c⊗c
  congIl-1 Il⊗c = refl
  congIl-1 ⊗r⊗c1 = ⊗r⊗c1
  congIl-1 ⊗r⊗c2 = ⊗r⊗c2

  cong⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
              {f g : just (A ⊗ B) ∣ Γ ⊢ C} →
              f ≗ g → ⊗l-1 f ≗ ⊗l-1 g
  cong⊗l-1 refl = refl
  cong⊗l-1 (~ p) = ~ cong⊗l-1 p
  cong⊗l-1 (p ∙ p₁) = cong⊗l-1 p ∙ cong⊗l-1 p₁
  cong⊗l-1 (⊗l p) = p
  cong⊗l-1 (⊗r p p₁) = ⊗r (cong⊗l-1 p) p₁
  cong⊗l-1 ax⊗ = refl
  cong⊗l-1 ⊗r⊗l = refl
  cong⊗l-1 (⊗c Γ Δ p) = ⊗c (_ ∷ Γ) Δ (cong⊗l-1 p)
  cong⊗l-1 ⊗c⊗c = ⊗c⊗c
  cong⊗l-1 ⊗l⊗c = refl
  cong⊗l-1 ⊗r⊗c1 = ⊗r⊗c1
  cong⊗l-1 ⊗r⊗c2 = ⊗r⊗c2

-- ====================================================================

-- Il-1 and ⊗l-1 are inverses up to ≗

abstract
  IlIl-1 : {Γ : Cxt} → {C : Fma} → 
                (f : just I ∣ Γ ⊢ C) → Il (Il-1 f) ≗ f
  IlIl-1 ax = ~ axI
  IlIl-1 (⊗r f f₁) = (~ ⊗rIl) ∙ (⊗r (IlIl-1 f) refl)
  IlIl-1 (Il f) = refl
  IlIl-1 (⊗c Γ Δ f) = Il⊗c ∙ ⊗c Γ Δ (IlIl-1 f)

  ⊗l⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
              (f : just (A ⊗ B) ∣ Γ ⊢ C) → ⊗l (⊗l-1 f) ≗ f
  ⊗l⊗l-1 ax = ~ ax⊗
  ⊗l⊗l-1 (⊗r f f₁) = (~ ⊗r⊗l) ∙ (⊗r (⊗l⊗l-1 f) refl)
  ⊗l⊗l-1 (⊗l f) = refl
  ⊗l⊗l-1 (⊗c Γ Δ f) = ⊗l⊗c ∙ ⊗c Γ Δ (⊗l⊗l-1 f)





