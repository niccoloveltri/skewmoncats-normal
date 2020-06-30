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

-- =======================================================================

-- Sequent calculus for right-normal skew monoidal categories

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
  Ic : {S : Stp} → (Γ Δ : Cxt) → {C : Fma} → 
              S ∣ Γ ++ Δ ⊢ C → S ∣ Γ ++ I ∷ Δ ⊢ C 
  ⊗c : {S : Stp} → (Γ Δ : Cxt) → {J J' C : Fma} (cJ : isCl J) (cJ' : isCl J') → 
              S ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C → S ∣ Γ ++ J ⊗ J' ∷ Δ ⊢ C 

subst-cxt : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subst-cxt refl f = f

-- ====================================================================

-- Being a closed formula is a property, i.e. proof-irrelevant.

uniq-cl : {J : Fma} (p q : isCl J) → p ≡ q
uniq-cl isI isI = refl
uniq-cl (is⊗ p p₁) (is⊗ q q₁) = begin
    is⊗ p p₁ ≡⟨ sym (cong (is⊗ p) (uniq-cl q₁ p₁)) ⟩
    is⊗ p q₁ ≡⟨ sym (cong (λ z → is⊗ z q₁) (uniq-cl q p)) ⟩ is⊗ q q₁ ∎

-- ====================================================================

-- In a derivable sequent with closed conclusion, both the optional
-- formula in the stoup and all formulae in the passive context are
-- closed too.

abstract
  mutual
    isCl-stp : {Γ : Cxt} {A J : Fma} → isCl J
      → just A ∣ Γ ⊢ J → isCl A
    isCl-stp cJ ax = cJ
    isCl-stp (is⊗ cJ cJ') (⊗r f f₁) = isCl-stp cJ f
    isCl-stp cJ (Il f) = isI
    isCl-stp cJ (⊗l f) = is⊗ (isCl-stp cJ f) (isCl-cxt [] cJ f refl)
    isCl-stp cJ (Ic Γ Δ f) = isCl-stp cJ f
    isCl-stp cJ (⊗c Γ Δ _ _ f) = isCl-stp cJ f

    isCl-cxt : {S : Stp} (Γ : Cxt) {Γ' Δ : Cxt} {A J : Fma} → isCl J
      → S ∣ Γ' ⊢ J → Γ' ≡ Γ ++ A ∷ Δ → isCl A
    isCl-cxt Γ cJ ax eq = ⊥-elim ([]disj∷ Γ eq)
    isCl-cxt Γ {Δ = Δ} cJ (uf {Γ₁} f) eq with cases∷ Γ eq
    isCl-cxt .[] {Δ = .Γ₁} cJ (uf {Γ₁} f) eq | inj₁ (refl , refl , refl) = isCl-stp cJ f
    isCl-cxt .(_ ∷ Γ₀) {Δ = Δ} cJ (uf {.(Γ₀ ++ _ ∷ Δ)} f) eq | inj₂ (Γ₀ , refl , refl) = isCl-cxt Γ₀ cJ f refl
    isCl-cxt Γ cJ Ir eq = ⊥-elim ([]disj∷ Γ eq)
    isCl-cxt Γ {Δ = Δ} (is⊗ cJ cJ') (⊗r {Γ = Γ₁} {Δ₁} f g) eq with cases++ Γ Γ₁ Δ Δ₁ eq
    isCl-cxt Γ {Δ = .(Γ₀ ++ Δ₁)} (is⊗ cJ cJ') (⊗r {Γ = .(Γ ++ _ ∷ Γ₀)} {Δ₁} f g) eq | inj₁ (Γ₀ , refl , refl) = isCl-cxt Γ cJ f refl
    isCl-cxt .(Γ₁ ++ Γ₀) {Δ = Δ} (is⊗ cJ cJ') (⊗r {Γ = Γ₁} {.(Γ₀ ++ _ ∷ Δ)} f g) eq | inj₂ (Γ₀ , refl , refl) = isCl-cxt Γ₀ cJ' g refl
    isCl-cxt Γ cJ (Il f) eq = isCl-cxt Γ cJ f eq
    isCl-cxt Γ cJ (⊗l f) refl = isCl-cxt (_ ∷ Γ) cJ f refl
    isCl-cxt Γ {Δ = Δ} cJ (Ic Γ₁ Δ₁ f) eq with cases++ Γ Γ₁ Δ (I ∷ Δ₁) eq
    isCl-cxt Γ {Δ = .(Γ₀ ++ I ∷ Δ₁)} cJ (Ic .(Γ ++ _ ∷ Γ₀) Δ₁ f) eq | inj₁ (Γ₀ , refl , refl) = isCl-cxt Γ cJ f refl
    isCl-cxt .Γ₁ {Δ = .Δ₁} cJ (Ic Γ₁ Δ₁ f) eq | inj₂ ([] , refl , refl) = isI
    isCl-cxt .(Γ₁ ++ I ∷ Γ₀) {Δ = Δ} cJ (Ic Γ₁ .(Γ₀ ++ _ ∷ Δ) f) eq | inj₂ (.I ∷ Γ₀ , refl , refl) = isCl-cxt (Γ₁ ++ Γ₀) cJ f refl
    isCl-cxt Γ {Δ = Δ} cJ (⊗c Γ₁ Δ₁ cK cK' f) eq with cases++ Γ Γ₁ Δ (_ ∷ Δ₁) eq
    isCl-cxt Γ {Δ = .(Γ₀ ++ _ ⊗ _ ∷ Δ₁)} cJ (⊗c .(Γ ++ _ ∷ Γ₀) Δ₁ cK cK' f) eq | inj₁ (Γ₀ , refl , refl) = isCl-cxt Γ cJ f refl
    isCl-cxt .Γ₁ {Δ = .Δ₁} cJ (⊗c Γ₁ Δ₁ cK cK' f) eq | inj₂ ([] , refl , refl) = is⊗ cK cK'
    isCl-cxt .(Γ₁ ++ _ ⊗ _ ∷ Γ₀) {Δ = Δ} cJ (⊗c Γ₁ .(Γ₀ ++ _ ∷ Δ) cK cK' f) eq | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) = isCl-cxt (Γ₁ ++ _ ∷ _ ∷ Γ₀) cJ f refl

-- ====================================================================

-- An interpretation of antecedents as contexts 

asCxt : Stp → Cxt → Cxt
asCxt nothing Γ = Γ
asCxt (just A) Γ = A ∷ Γ

asCxt++ : (S : Stp)(Γ Δ : Cxt)
  → asCxt S (Γ ++ Δ) ≡ asCxt S Γ ++ Δ
asCxt++ nothing Γ Δ = refl
asCxt++ (just S) Γ Δ = refl  

{-# REWRITE asCxt++ #-}

-- ====================================================================

-- Inverted left rules

Il-1 : {Γ : Cxt} → {C : Fma} → 
              just I ∣ Γ ⊢ C → nothing ∣ Γ ⊢ C
Il-1 ax = Ir
Il-1 (⊗r f f₁) = ⊗r (Il-1 f) f₁
Il-1 (Il f) = f
Il-1 (Ic Γ Δ f) = Ic Γ Δ (Il-1 f)              
Il-1 (⊗c Γ Δ cJ cJ' f) = ⊗c Γ Δ cJ cJ' (Il-1 f)              

⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
            just (A ⊗ B) ∣ Γ ⊢ C → just A ∣ B ∷ Γ ⊢ C
⊗l-1 ax = ⊗r ax (uf ax)
⊗l-1 (⊗r f f₁) = ⊗r (⊗l-1 f) f₁
⊗l-1 (⊗l f) = f
⊗l-1 (Ic Γ Δ f) = Ic (_ ∷ Γ) Δ (⊗l-1 f)
⊗l-1 (⊗c Γ Δ cJ cJ' f) = ⊗c (_ ∷ Γ) Δ cJ cJ' (⊗l-1 f)              


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
 
  Ic : ∀{S} Γ Δ {C}{f g : S ∣ Γ ++ Δ ⊢ C}
    → f ≗ g → Ic Γ Δ f ≗ Ic Γ Δ g
  ufIc1 : {Γ : Cxt} {C : Fma}
    → {f : nothing ∣ Γ ⊢ C}
    → uf (Il f) ≗ Ic [] Γ f
  IcIc : {S : Stp} {Γ Δ Λ : Cxt} {C : Fma}
    → {f : S ∣ Γ ++ Δ ++ Λ ⊢ C}
    → Ic Γ (Δ ++ I ∷ Λ) (Ic (Γ ++ Δ) Λ f)
          ≗ Ic (Γ ++ I ∷ Δ) Λ (Ic Γ (Δ ++ Λ) f)
  ⊗cIc : {S : Stp} {Γ Δ Λ : Cxt} {C J J' : Fma}
    → {cJ : isCl J}{cJ' : isCl J'}
    → {f : S ∣ Γ ++ J ∷ J' ∷ Δ ++ Λ ⊢ C}
    → ⊗c Γ (Δ ++ I ∷ Λ) cJ cJ' (Ic (Γ ++ J ∷ J' ∷ Δ) Λ f)
          ≗ Ic (Γ ++ J ⊗ J' ∷ Δ) Λ (⊗c Γ (Δ ++ Λ) cJ cJ' f)
  ufIc2 : {Γ Δ : Cxt} {A C : Fma}
    → {f : just A ∣ Γ ++ Δ ⊢ C}
    → uf (Ic Γ Δ f) ≗ Ic (A ∷ Γ) Δ (uf f)
  IlIc : {Γ Δ : Cxt} {C : Fma}
    → {f : nothing ∣ Γ ++ Δ ⊢ C}
    → Il (Ic Γ Δ f) ≗ Ic Γ Δ (Il f)
  ⊗lIc : {Γ Δ : Cxt} {A B C : Fma}
    → {f : just A ∣ B ∷ Γ ++ Δ ⊢ C}
    → ⊗l (Ic (B ∷ Γ) Δ f) ≗ Ic Γ Δ (⊗l f)
  ⊗rIc1 : {S : Stp}{Γ Γ' Δ : Cxt}{A B : Fma}
    → {f : S ∣ Γ ++ Γ' ⊢ A} {g : nothing ∣ Δ ⊢ B}
    → ⊗r (Ic Γ Γ' f) g ≗ Ic Γ (Γ' ++ Δ) (⊗r f g)
  ⊗rIc2 : {S : Stp}{Γ Δ Δ' : Cxt}{A B : Fma}
    → {f : S ∣ Γ ⊢ A} {g : nothing ∣ Δ ++ Δ' ⊢ B}
    → ⊗r f (Ic Δ Δ' g) ≗ Ic (Γ ++ Δ) Δ' (⊗r f g)

  ⊗c : ∀{S} Γ Δ {C J J'} (cJ : isCl J) (cJ' : isCl J')
    → {f g : S ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C}
    → f ≗ g → ⊗c Γ Δ cJ cJ' f ≗ ⊗c Γ Δ cJ cJ' g
  uf⊗c1 : {Γ : Cxt} {C J J' : Fma} {cJ : isCl J} {cJ' : isCl J'}
    → {f : just J ∣ J' ∷ Γ ⊢ C}
    → uf (⊗l f) ≗ ⊗c [] Γ cJ cJ' (uf f)
  ⊗c⊗c : {S : Stp} {Γ Δ Λ : Cxt} {C J J' K K' : Fma}
    → {cJ : isCl J} {cJ' : isCl J'}{cK : isCl K} {cK' : isCl K'}
    → {f : S ∣ Γ ++ J ∷ J' ∷ Δ ++ K ∷ K' ∷ Λ ⊢ C}
    → ⊗c Γ (Δ ++ K ⊗ K' ∷ Λ) cJ cJ' (⊗c (Γ ++ J ∷ J' ∷ Δ) Λ cK cK' f)
          ≗ ⊗c (Γ ++ J ⊗ J' ∷ Δ) Λ cK cK' (⊗c Γ (Δ ++ K ∷ K' ∷ Λ) cJ cJ' f)
  Ic⊗c : {S : Stp} {Γ Δ Λ : Cxt} {C J J' : Fma}
    → {cJ : isCl J}{cJ' : isCl J'}
    → {f : S ∣ Γ ++ Δ ++ J ∷ J' ∷ Λ ⊢ C}
    → Ic Γ (Δ ++ J ⊗ J' ∷ Λ) (⊗c (Γ ++ Δ) Λ cJ cJ' f)
          ≗ ⊗c (Γ ++ I ∷ Δ) Λ cJ cJ' (Ic Γ (Δ ++ J ∷ J' ∷ Λ) f)
  uf⊗c2 : {Γ Δ : Cxt} {A C J J' : Fma}
    → {cJ : isCl J}{cJ' : isCl J'}
    → {f : just A ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C}
    → uf (⊗c Γ Δ cJ cJ' f) ≗ ⊗c (A ∷ Γ) Δ cJ cJ' (uf f)
  Il⊗c : {Γ Δ : Cxt} {C J J' : Fma}
    → {cJ : isCl J}{cJ' : isCl J'}
    → {f : nothing ∣ Γ ++ J ∷ J' ∷ Δ ⊢ C}
    → Il (⊗c Γ Δ cJ cJ' f) ≗ ⊗c Γ Δ cJ cJ' (Il f)
  ⊗l⊗c : {Γ Δ : Cxt} {A B C J J' : Fma}
    → {cJ : isCl J}{cJ' : isCl J'}
    → {f : just A ∣ B ∷ Γ ++ J ∷ J' ∷ Δ ⊢ C}
    → ⊗l (⊗c (B ∷ Γ) Δ cJ cJ' f) ≗ ⊗c Γ Δ cJ cJ' (⊗l f)
  ⊗r⊗c1 : {S : Stp}{Γ Γ' Δ : Cxt}{A B J J' : Fma}
    → {cJ : isCl J}{cJ' : isCl J'}
    → {f : S ∣ Γ ++ J ∷ J' ∷ Γ' ⊢ A} {g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗c Γ Γ' cJ cJ' f) g ≗ ⊗c Γ (Γ' ++ Δ) cJ cJ' (⊗r f g)
  ⊗r⊗c2 : {S : Stp}{Γ Δ Δ' : Cxt}{A B J J' : Fma}
    → {cJ : isCl J}{cJ' : isCl J'}
    → {f : S ∣ Γ ⊢ A} {g : nothing ∣ Δ ++ J ∷ J' ∷ Δ' ⊢ B}
    → ⊗r f (⊗c Δ Δ' cJ cJ' g) ≗ ⊗c (Γ ++ Δ) Δ' cJ cJ' (⊗r f g)

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
  congIl-1 (Ic Γ Δ p) = Ic Γ Δ (congIl-1 p)
  congIl-1 IcIc = IcIc
  congIl-1 ⊗cIc = ⊗cIc
  congIl-1 IlIc = refl
  congIl-1 ⊗rIc1 = ⊗rIc1
  congIl-1 ⊗rIc2 = ⊗rIc2
  congIl-1 (⊗c Γ Δ cJ cJ' p) = ⊗c Γ Δ cJ cJ' (congIl-1 p)
  congIl-1 ⊗c⊗c = ⊗c⊗c
  congIl-1 Ic⊗c = Ic⊗c
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
  cong⊗l-1 (Ic Γ Δ p) = Ic (_ ∷ Γ) Δ (cong⊗l-1 p)
  cong⊗l-1 IcIc = IcIc
  cong⊗l-1 ⊗cIc = ⊗cIc
  cong⊗l-1 ⊗lIc = refl
  cong⊗l-1 ⊗rIc1 = ⊗rIc1
  cong⊗l-1 ⊗rIc2 = ⊗rIc2
  cong⊗l-1 (⊗c Γ Δ cJ cJ' p) = ⊗c (_ ∷ Γ) Δ cJ cJ' (cong⊗l-1 p)
  cong⊗l-1 ⊗c⊗c = ⊗c⊗c
  cong⊗l-1 Ic⊗c = Ic⊗c
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
  IlIl-1 (Ic Γ Δ f) = IlIc ∙ Ic Γ Δ (IlIl-1 f)
  IlIl-1 (⊗c Γ Δ cJ cj' f) = Il⊗c ∙ ⊗c Γ Δ cJ cj' (IlIl-1 f)

  ⊗l⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
              (f : just (A ⊗ B) ∣ Γ ⊢ C) → ⊗l (⊗l-1 f) ≗ f
  ⊗l⊗l-1 ax = ~ ax⊗
  ⊗l⊗l-1 (⊗r f f₁) = (~ ⊗r⊗l) ∙ (⊗r (⊗l⊗l-1 f) refl)
  ⊗l⊗l-1 (⊗l f) = refl
  ⊗l⊗l-1 (Ic Γ Δ f) = ⊗lIc ∙ Ic Γ Δ (⊗l⊗l-1 f)
  ⊗l⊗l-1 (⊗c Γ Δ cJ cj' f) = ⊗l⊗c ∙ ⊗c Γ Δ cJ cj' (⊗l⊗l-1 f)





