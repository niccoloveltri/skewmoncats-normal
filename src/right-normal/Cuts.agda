{-# OPTIONS --rewriting #-}

module Cuts where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Fsk
open import SeqCalc

-- ===============================================================

-- Admissible cut rules, plus some laws of cuts

-- ===============================================================

-- A special form of weakening: formulae can be removed from the
-- passive context in case the unit I is derivable from them. This
-- looks like the I-elimination rule of linear lambda calculus.

letI : {T S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {C : Fma}
  → T ∣ Γ ⊢ I →  S ∣ Δ₀ ++ Δ₁ ⊢ C
  → S ∣ Δ₀ ++ asCxt T Γ ++ Δ₁ ⊢ C
letI Δ₀ Δ₁ ax g = Ic Δ₀ Δ₁ g
letI Δ₀ Δ₁ (uf f) g = letI Δ₀ Δ₁ f g
letI Δ₀ Δ₁ Ir g = g
letI Δ₀ Δ₁ (Il f) g =
  Ic Δ₀ (_ ++ Δ₁) (letI Δ₀ Δ₁ f g)
letI Δ₀ Δ₁ (⊗l f) g =
  ⊗c Δ₀ (_ ++ Δ₁) (isCl-stp isI f) (isCl-cxt [] isI f refl) (letI Δ₀ Δ₁ f g)
letI {T} Δ₀ Δ₁ (Ic Γ Δ f) g =
  Ic (Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁) (letI Δ₀ Δ₁ f g)
letI {T} Δ₀ Δ₁ (⊗c Γ Δ cJ cJ' f) g =
  ⊗c (Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁) cJ cJ' (letI Δ₀ Δ₁ f g)

-- The admissible cut rules, constructed simultaneously with another
-- special substitution, which looks like the ⊗-elimination rule of
-- linear lambda calculus.

mutual
  scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
              S ∣ Γ ⊢ A  →  just A ∣ Δ' ⊢ C  →  S ∣ Γ ++ Δ' ⊢ C
  scut ax g = g
  scut (uf f) g = uf (scut f g)
  scut Ir ax = Ir
  scut Ir (⊗r g g₁) = ⊗r (scut Ir g) g₁
  scut Ir (Il g) = g
  scut Ir (Ic Γ Δ g) = Ic Γ Δ (scut Ir g)
  scut Ir (⊗c Γ Δ cJ cJ' g) = ⊗c Γ Δ cJ cJ' (scut Ir g)
  scut (⊗r f f₁) ax = ⊗r f f₁
  scut (⊗r f f₁) (⊗r g g₁) = ⊗r (scut (⊗r f f₁) g) g₁
  scut (⊗r f f₁) (⊗l g) = scut f (ccut [] f₁ g refl) 
  scut (⊗r {Γ = Γ₁} {Δ₁} f f₁) (Ic Γ Δ g) = Ic (Γ₁ ++ Δ₁ ++ Γ) Δ (scut (⊗r f f₁) g)
  scut (⊗r {Γ = Γ₁} {Δ₁} f f₁) (⊗c Γ Δ cJ cJ' g) = ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ cJ cJ' (scut (⊗r f f₁) g)
  scut (Il f) g = Il (scut f g)
  scut (⊗l f) g = ⊗l (scut f g)
  scut {Δ' = Δ'} (Ic Γ Δ f) g = Ic Γ (Δ ++ Δ') (scut f g)
  scut {Δ' = Δ'} (⊗c Γ Δ cJ cJ' f) g = ⊗c Γ (Δ ++ Δ') cJ cJ' (scut f g)
  
  ccut : {T S : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             T ∣ Γ ⊢ A  →  S ∣ Δ ⊢ C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        S ∣ Δ₀ ++ asCxt T Γ ++ Δ' ⊢ C
  ccut Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut Δ₀ f (uf g) p with cases∷ Δ₀ p 
  ccut {nothing} .[] f (uf g) p | inj₁ (refl , refl , refl) = scut f g
  ccut {just A} .[] f (uf g) p | inj₁ (refl , refl , refl) = uf (scut f g) 
  ccut .(_ ∷ Δ₀) f (uf g) p | inj₂ (Δ₀ , r , refl) =  uf (ccut Δ₀ f g r)
  ccut Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
  ccut Δ₀ f (⊗r g g') p | inj₁ (Γ₀ , refl , refl) = ⊗r (ccut Δ₀ f g refl) g'
  ccut ._ f (⊗r g g') p | inj₂ (Γ₀ , refl , refl) = ⊗r g (ccut Γ₀  f g' refl)
  ccut Δ₀ f (Il g) r = Il (ccut Δ₀ f g r)
  ccut Δ₀ f (⊗l {B = B} g) r = ⊗l (ccut (B ∷ Δ₀) f g (cong (_∷_ B) r))
  ccut Δ₀ {Δ'} f (Ic Γ Δ g) r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
  ccut {T} {Γ = Γ} Δ₀ {.(Γ₀ ++ I ∷ Δ)} f (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) r | inj₁ (Γ₀ , refl , refl) =
    Ic (Δ₀ ++ asCxt T Γ ++ Γ₀) Δ (ccut Δ₀ f g refl)
  ccut .Γ {.Δ} f (Ic Γ Δ g) refl | inj₂ ([] , refl , refl) = letI Γ Δ f g
  ccut {T} {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} f (Ic Γ .(Γ₀ ++ _ ∷ Δ') g) r | inj₂ (.I ∷ Γ₀ , refl , refl) =
    Ic Γ (Γ₀ ++ asCxt T Γ₁ ++ Δ') (ccut (Γ ++ Γ₀) f g refl)
  ccut Δ₀ {Δ'} f (⊗c Γ Δ {J} {J'} cJ cJ' g) r with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) r
  ccut {T} {Γ = Γ} Δ₀ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ {J} {J'} cJ cJ' g) r | inj₁ (Γ₀ , refl , refl) =
    ⊗c (Δ₀ ++ asCxt T Γ ++ Γ₀) Δ cJ cJ' (ccut Δ₀ f g refl)
  ccut .Γ {.Δ} f (⊗c Γ Δ {J} {J'} cJ cJ' g) refl | inj₂ ([] , refl , refl) = let⊗ Γ Δ cJ cJ' f g 
  ccut {T} {Γ = Γ₁} .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') {J} {J'} cJ cJ' g) r | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) =
    ⊗c Γ (Γ₀ ++ asCxt T Γ₁ ++ Δ') cJ cJ' (ccut (Γ ++ J ∷ J' ∷ Γ₀) f g refl)

  let⊗ : {T S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {C J J' : Fma}
    → (cJ : isCl J) (cJ' : isCl J')
    → T ∣ Γ ⊢ J ⊗ J' →  S ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C
    → S ∣ Δ₀ ++ asCxt T Γ ++ Δ₁ ⊢ C
  let⊗ Δ₀ Δ₁ cJ cJ' (uf f) g = let⊗ Δ₀ Δ₁ cJ cJ' f g
  let⊗ Δ₀ Δ₁ cJ cJ' (⊗r f f') g = ccut Δ₀ f (ccut (Δ₀ ++ _ ∷ []) f' g refl) refl
  let⊗ {T} Δ₀ Δ₁ cJ cJ' (Ic Γ Δ f) g = Ic (Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁) (let⊗ Δ₀ Δ₁ cJ cJ' f g)
  let⊗ {T} Δ₀ Δ₁ cJ cJ' (⊗c Γ Δ cK cK' f) g = ⊗c (Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁) cK cK' (let⊗ Δ₀ Δ₁ cJ cJ' f g)
  let⊗ Δ₀ Δ₁ cJ cJ' ax g = ⊗c Δ₀ Δ₁ cJ cJ' g
  let⊗ {Γ = Γ} Δ₀ Δ₁ cJ cJ' (Il f) g = Ic Δ₀ (Γ ++ Δ₁) (let⊗ Δ₀ Δ₁ cJ cJ' f g)
  let⊗ {Γ = Γ} Δ₀ Δ₁ cJ cJ' (⊗l f) g =
    ⊗c Δ₀ (Γ ++ Δ₁) (isCl-stp (is⊗ cJ cJ') f) (isCl-cxt [] (is⊗ cJ cJ') f refl) (let⊗ Δ₀ Δ₁ cJ cJ' f g)

-- ====================================================================

-- some lemmata about scut and ⊗r

abstract
  scut⊗ruf : {Γ Δ Δ' : Cxt}{A A' B C : Fma}
    → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → (f' : just (A ⊗ B) ∣ Δ' ⊢ C)
    → scut (⊗r (uf f) g) f' ≗ uf (scut (⊗r f g) f')
  scut⊗ruf ax = ⊗ruf
  scut⊗ruf {f = f}{g} (⊗r h h') =
    proof≗
    ⊗r (scut (⊗r (uf f) g) h) h'
    ≗〈 ⊗r (scut⊗ruf h) refl 〉
    ⊗r (uf (scut (⊗r f g) h)) h'
    ≗〈 ⊗ruf 〉
    uf (⊗r (scut (⊗r f g) h) h')
    qed≗
  scut⊗ruf (⊗l h) = refl
  scut⊗ruf {Γ₁} {Δ₁} (Ic Γ Δ f) =
    Ic (_ ∷ Γ₁ ++ Δ₁ ++ Γ) Δ (scut⊗ruf f)
    ∙ ~ ufIc2 {Γ = Γ₁ ++ Δ₁ ++ Γ} {Δ}
  scut⊗ruf {Γ₁} {Δ₁} (⊗c Γ Δ cJ cJ' f) =
    ⊗c (_ ∷ Γ₁ ++ Δ₁ ++ Γ) Δ cJ cJ' (scut⊗ruf f)
    ∙ (~ uf⊗c2 {Γ = Γ₁ ++ Δ₁ ++ Γ} {Δ})
  
  scut⊗rIl : {Γ Δ Δ' : Cxt}{A B C : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
    → scut (⊗r (Il f) g) h ≗ Il (scut (⊗r f g) h)
  scut⊗rIl ax = ⊗rIl
  scut⊗rIl {f = f}{g}(⊗r h h') =
    proof≗
    ⊗r (scut (⊗r (Il f) g) h) h'
    ≗〈 ⊗r (scut⊗rIl h) refl 〉
    ⊗r (Il (scut (⊗r f g) h)) h'
    ≗〈 ⊗rIl 〉
    Il (⊗r (scut (⊗r f g) h) h')
    qed≗
  scut⊗rIl (⊗l h) = refl
  scut⊗rIl {Γ₁} {Δ₁} (Ic Γ Δ h) =
    Ic (Γ₁ ++ Δ₁ ++ Γ) Δ (scut⊗rIl h)
    ∙ (~ IlIc {Γ = Γ₁ ++ Δ₁ ++ Γ})
  scut⊗rIl {Γ₁} {Δ₁} (⊗c Γ Δ cJ cJ' h) =
    ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ cJ cJ' (scut⊗rIl h)
    ∙ (~ Il⊗c {Γ = Γ₁ ++ Δ₁ ++ Γ})
  
  scut⊗r⊗l : {Γ Δ Δ' : Cxt}{A A' B B' C : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
    → scut (⊗r (⊗l f) g) h ≗ ⊗l (scut (⊗r f g) h)
  scut⊗r⊗l ax = ⊗r⊗l
  scut⊗r⊗l {f = f}{g} (⊗r h h') =
    proof≗
    ⊗r (scut (⊗r (⊗l f) g) h) h'
    ≗〈 ⊗r (scut⊗r⊗l h) refl 〉
    ⊗r (⊗l (scut (⊗r f g) h)) h'
    ≗〈 ⊗r⊗l 〉
    ⊗l (⊗r (scut (⊗r f g) h) h')
    qed≗
  scut⊗r⊗l (⊗l h) = refl
  scut⊗r⊗l {Γ₁} {Δ₁} (Ic Γ Δ h) =
    Ic (Γ₁ ++ Δ₁ ++ Γ) Δ (scut⊗r⊗l h)
    ∙ ~ ⊗lIc {Γ = Γ₁ ++ Δ₁ ++ Γ}
  scut⊗r⊗l {Γ₁} {Δ₁} (⊗c Γ Δ cJ cJ' h) = 
    ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ cJ cJ' (scut⊗r⊗l h)
    ∙ ~ ⊗l⊗c {Γ = Γ₁ ++ Δ₁ ++ Γ}
  
  scut⊗r : ∀{S}{Γ}{Δ}{Δ'}{A}{B}{C}
    → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(g' : nothing ∣ Δ' ⊢ C)
    → scut f (⊗r g g') ≗ ⊗r (scut f g) g'
  scut⊗r ax g g' = refl
  scut⊗r (uf f) g g' =
    proof≗
    uf (scut f (⊗r g g'))
    ≗〈 uf (scut⊗r f g g') 〉 
    uf (⊗r (scut f g) g')
    ≗〈 ~ ⊗ruf 〉 
    ⊗r (uf (scut f g)) g'
    qed≗
  scut⊗r Ir g g' = refl
  scut⊗r (⊗r f f') g g' = refl
  scut⊗r (Il f) g g' =
    proof≗
    Il (scut f (⊗r g g'))
    ≗〈 Il (scut⊗r f g g') 〉 
    Il (⊗r (scut f g) g')
    ≗〈 ~ ⊗rIl 〉 
    ⊗r (Il (scut f g)) g'
    qed≗
  scut⊗r (⊗l f) g g' =
    proof≗
    ⊗l (scut f (⊗r g g'))
    ≗〈 ⊗l (scut⊗r f g g') 〉 
    ⊗l (⊗r (scut f g) g')
    ≗〈 ~ ⊗r⊗l 〉 
    ⊗r (⊗l (scut f g)) g'
    qed≗
  scut⊗r {Δ = Δ₁} {Δ'} (Ic Γ Δ f) g g' =
    Ic Γ (Δ ++ Δ₁ ++ Δ') (scut⊗r f g g')
    ∙ ~ ⊗rIc1 
  scut⊗r {Δ = Δ₁} {Δ'} (⊗c Γ Δ cJ cJ' f) g g' = 
    ⊗c Γ (Δ ++ Δ₁ ++ Δ') cJ cJ' (scut⊗r f g g')
    ∙ ~ ⊗r⊗c1 

-- unitality of identity wrt. cut

abstract
  ccut-unit : {T : Stp}{Γ Δ : Cxt}(Δ₀ : Cxt){A C : Fma}
    → (g : T ∣ Δ ⊢ C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
    → ccut Δ₀ (uf ax) g r ≡ subst-cxt r g
  ccut-unit Δ₀ ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-unit Δ₀ (uf g) r with cases∷ Δ₀ r
  ccut-unit .[] (uf g) refl | inj₁ (refl , refl , refl) = refl
  ccut-unit .(_ ∷ Γ) (uf g) refl | inj₂ (Γ , refl , refl) = cong uf (ccut-unit Γ g refl)
  ccut-unit Δ₀ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-unit {_}{Γ} Δ₀ (⊗r {Γ = Γ'}{Δ} g g') r with cases++ Δ₀ Γ' Γ Δ r
  ccut-unit Δ₀ (⊗r {Γ = Γ}{Δ} g g') refl | inj₁ (Γ₀ , refl , refl) = 
    cong₂ (⊗r {Γ = Γ}{Δ}) (ccut-unit Δ₀ g refl) refl
  ccut-unit ._ (⊗r {Γ = Γ}{Δ} g g') refl | inj₂ (Δ₀ , refl , refl) =
    cong₂ (⊗r {Γ = Γ}) refl (ccut-unit Δ₀ g' refl)
  ccut-unit Δ₀ (Il g) refl = cong Il (ccut-unit Δ₀ g refl)
  ccut-unit Δ₀ (⊗l g) refl = cong ⊗l (ccut-unit (_ ∷ Δ₀) g refl)
  ccut-unit {Γ = Γ₁} Δ₀ (Ic Γ Δ g) r with cases++ Δ₀ Γ Γ₁ (I ∷ Δ) r
  ccut-unit {Γ = .(Γ₀ ++ I ∷ Δ)} Δ₀ (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
    cong (Ic (Δ₀ ++ _ ∷ Γ₀) Δ) (ccut-unit Δ₀ g refl)
  ccut-unit {Γ = .Δ} .Γ (Ic Γ Δ g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ Δ I = refl
  ccut-unit {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) (Ic Γ .(Γ₀ ++ _ ∷ Γ₁) g) refl | inj₂ (_ ∷ Γ₀ , refl , refl) =
    cong (Ic Γ (Γ₀ ++ _ ∷ Γ₁)) (ccut-unit (Γ ++ Γ₀) g refl)
  ccut-unit {Γ = Γ₁} Δ₀ (⊗c Γ Δ cJ cj' g) r with cases++ Δ₀ Γ Γ₁ (_ ⊗ _ ∷ Δ) r
  ccut-unit {Γ = .(Γ₀ ++ _ ⊗ _ ∷ Δ)} Δ₀ (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ cJ cj' g) refl | inj₁ (Γ₀ , refl , refl) =
    cong (⊗c (Δ₀ ++ _ ∷ Γ₀) Δ cJ cj') (ccut-unit Δ₀ g refl)
  ccut-unit {Γ = .Δ} .Γ (⊗c Γ Δ {J = J}{J'} cJ cj' g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ Δ (J ⊗ J') = refl
  ccut-unit {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) (⊗c Γ .(Γ₀ ++ _ ∷ Γ₁) cJ cj' g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    cong (⊗c Γ (Γ₀ ++ _ ∷ Γ₁) cJ cj') (ccut-unit (Γ ++ _ ∷ _ ∷ Γ₀) g refl)
  
  scut-unit : {S : Stp}{Γ : Cxt}{A : Fma}(f : S ∣ Γ ⊢ A) → scut f ax ≡ f
  scut-unit ax = refl
  scut-unit (uf f) = cong uf (scut-unit f)
  scut-unit Ir = refl
  scut-unit (⊗r f f') = refl
  scut-unit (Il f) = cong Il (scut-unit f)
  scut-unit (⊗l f) = cong ⊗l (scut-unit f)
  scut-unit (Ic Γ Δ f) = cong (Ic Γ Δ) (scut-unit f)
  scut-unit (⊗c Γ Δ cJ cJ' f) = cong (⊗c Γ Δ cJ cJ') (scut-unit f)

-- ====================================================================

-- the cut rules, and also letI and let⊗, commute with Il-1 and ⊗-1

abstract
  letI-Il-1 : ∀{T}{Γ}{C} Δ₀ Δ₁ 
    → (f : T ∣ Γ ⊢ I)(g : just I ∣ Δ₀ ++ Δ₁ ⊢ C)
    → Il-1 (letI Δ₀ Δ₁ f g) ≡ letI Δ₀ Δ₁ f (Il-1 g)
  letI-Il-1 Δ₀ Δ₁ (uf f) g = letI-Il-1 Δ₀ Δ₁ f g 
  letI-Il-1 Δ₀ Δ₁ Ir g = refl
  letI-Il-1 {T} Δ₀ Δ₁ (Ic Γ Δ f) g = cong (Ic (Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁)) (letI-Il-1 Δ₀ Δ₁ f g)
  letI-Il-1 {T} Δ₀ Δ₁ (⊗c Γ Δ cJ cJ' f) g = cong (⊗c (Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁) cJ cJ') (letI-Il-1 Δ₀ Δ₁ f g)
  letI-Il-1 Δ₀ Δ₁ ax g = refl
  letI-Il-1 {Γ = Γ} Δ₀ Δ₁ (Il f) g = cong (Ic Δ₀ (Γ ++ Δ₁)) (letI-Il-1 Δ₀ Δ₁ f g)
  letI-Il-1 {Γ = Γ} Δ₀ Δ₁ (⊗l f) g = cong (⊗c Δ₀ (Γ ++ Δ₁) _ _) (letI-Il-1 Δ₀ Δ₁ f g)

abstract
  mutual
    ccut-Il-1 : ∀{T}{Γ}{Δ}{A}{C} Δ₀ {Δ'}
      → (f : T ∣ Γ ⊢ A)(g : just I ∣ Δ ⊢ C)
      → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
      → Il-1 (ccut Δ₀ f g r) ≡ ccut Δ₀ f (Il-1 g) r
    ccut-Il-1 Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-Il-1 {Γ = Γ} Δ₀ {Δ'} f (⊗r {Γ = Γ'}{Δ} g g') r with cases++ Δ₀ Γ' Δ' Δ r
    ccut-Il-1 {T}{Γ} Δ₀ {_} f (⊗r {Γ = _} {Δ} g g') r | inj₁ (Γ₀ , refl , refl) = 
      cong₂ (⊗r {Γ = Δ₀ ++ asCxt T Γ ++ Γ₀}{Δ}) (ccut-Il-1 Δ₀  f g refl) refl
    ccut-Il-1 ._ f (⊗r g g') r | inj₂ (Γ₀ , refl , refl) = refl
    ccut-Il-1 Δ₀ f (Il g) r = refl
    ccut-Il-1 Δ₀ {Δ'} f (Ic Γ Δ g) r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    ccut-Il-1 {T}{Γ} Δ₀ {.(Γ₀ ++ I ∷ Δ)} f (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
      cong (Ic (Δ₀ ++ asCxt T Γ ++ Γ₀) Δ) (ccut-Il-1 Δ₀ f g refl)
    ccut-Il-1 .Γ {.Δ} f (Ic Γ Δ g) refl | inj₂ ([] , refl , refl) = letI-Il-1 Γ Δ f g 
    ccut-Il-1 {T}{Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} f (Ic Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.I ∷ Γ₀ , refl , refl) =
      cong (Ic Γ (Γ₀ ++ asCxt T Γ₁ ++ Δ')) (ccut-Il-1 (Γ ++ Γ₀) f g refl)
    ccut-Il-1 Δ₀ {Δ'} f (⊗c Γ Δ cJ cJ' g) r with cases++ Δ₀ Γ Δ' (_ ⊗ _ ∷ Δ) r
    ccut-Il-1 {T}{Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ cJ cJ' g) refl | inj₁ (Γ₀ , refl , refl) =
      cong (⊗c (Δ₀ ++ asCxt T Γ ++ Γ₀) Δ cJ cJ') (ccut-Il-1 Δ₀ f g refl)
    ccut-Il-1 .Γ {.Δ} f (⊗c Γ Δ cJ cJ' g) refl | inj₂ ([] , refl , refl) = let⊗-Il-1 Γ Δ f g  
    ccut-Il-1 {T}{Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') cJ cJ' g) refl | inj₂ (._ ∷ Γ₀ , refl , refl) =
      cong (⊗c Γ (Γ₀ ++ asCxt T Γ₁ ++ Δ') cJ cJ') (ccut-Il-1 (Γ ++ _ ∷ _ ∷ Γ₀) f g refl)
      
    let⊗-Il-1 : ∀{T}{Γ}{C J J'} Δ₀ Δ₁ {cJ : isCl J} {cJ' : isCl J'}
      → (f : T ∣ Γ ⊢ J ⊗ J')(g : just I ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
      → Il-1 (let⊗ Δ₀ Δ₁ cJ cJ' f g) ≡ let⊗ Δ₀ Δ₁ cJ cJ' f (Il-1 g)
    let⊗-Il-1 Δ₀ Δ₁ (uf f) g = let⊗-Il-1 Δ₀ Δ₁ f g 
    let⊗-Il-1 Δ₀ Δ₁ (⊗r f f') g =
      trans (ccut-Il-1 Δ₀  f (ccut (Δ₀ ++ _ ∷ []) f' g refl) refl)
        (cong (λ x → ccut Δ₀ f x refl) (ccut-Il-1  (Δ₀ ++ _ ∷ []) f' g refl))
    let⊗-Il-1 {T} Δ₀ Δ₁ (Ic Γ Δ f) g = cong (Ic (Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁)) (let⊗-Il-1 Δ₀ Δ₁ f g)
    let⊗-Il-1 {T} Δ₀ Δ₁ (⊗c Γ Δ cJ₁ cJ'' f) g = cong (⊗c (Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁) cJ₁ cJ'') (let⊗-Il-1 Δ₀ Δ₁ f g)
    let⊗-Il-1 Δ₀ Δ₁ ax g = refl
    let⊗-Il-1 {T}{Γ} Δ₀ Δ₁ (Il f) g = cong (Ic Δ₀ (Γ ++ Δ₁)) (let⊗-Il-1 Δ₀ Δ₁ f g)
    let⊗-Il-1 {T}{Γ} Δ₀ Δ₁ (⊗l f) g = cong (⊗c Δ₀ (Γ ++ Δ₁) _ _) (let⊗-Il-1 Δ₀ Δ₁ f g)

abstract
  Il-1-scutIr : {Γ : Cxt} → {C : Fma}
    → (f : just I ∣ Γ ⊢ C)
    → Il-1 f ≡ scut Ir f
  Il-1-scutIr ax = refl
  Il-1-scutIr (⊗r {Γ = Γ} {Δ} f f₁) =
    cong₂ (⊗r {Γ = Γ} {Δ}) (Il-1-scutIr f) refl
  Il-1-scutIr (Il f) = refl
  Il-1-scutIr (Ic Γ Δ f) = cong (Ic Γ Δ) (Il-1-scutIr f)
  Il-1-scutIr (⊗c Γ Δ cJ cJ' f) = cong (⊗c Γ Δ cJ cJ') (Il-1-scutIr f)

  scutIl-1 : {Γ Δ : Cxt} → {A C : Fma}
    → (f : just I ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ C)
    → Il-1 (scut f g) ≡ scut (Il-1 f) g
  scutIl-1 ax g = Il-1-scutIr g
  scutIl-1 (⊗r f f') ax = refl
  scutIl-1 (⊗r {Γ = Γ} {Δ} f f') (⊗r {Γ = Γ₁} {Δ₁} g g') =
    cong₂ (⊗r {Γ = Γ ++ Δ ++ Γ₁}{Δ₁}) (scutIl-1 (⊗r f f') g) refl
  scutIl-1 (⊗r {Γ = Γ} f f') (⊗l g) = scutIl-1 f (ccut [] f' g refl)
  scutIl-1 (⊗r {Γ = Γ} {Δ} f f') (Ic Γ' Δ' g) =
    cong (Ic (Γ ++ Δ ++ Γ') Δ') (scutIl-1 (⊗r f f') g)
  scutIl-1 (⊗r {Γ = Γ} {Δ} f f') (⊗c Γ' Δ' cJ cJ' g) =
    cong (⊗c (Γ ++ Δ ++ Γ') Δ' cJ cJ') (scutIl-1 (⊗r f f') g)
  scutIl-1 (Il f) g = refl
  scutIl-1 {Δ = Δ₁} (Ic Γ Δ f) g = cong (Ic Γ (Δ ++ Δ₁)) (scutIl-1 f g)
  scutIl-1 {Δ = Δ₁} (⊗c Γ Δ cJ cJ' f) g = cong (⊗c Γ (Δ ++ Δ₁) cJ cJ') (scutIl-1 f g)

abstract
  letI-⊗l-1 : ∀{T}{Γ}{A B C} Δ₀ Δ₁ 
    → (f : T ∣ Γ ⊢ I)(g : just (A ⊗ B) ∣ Δ₀ ++ Δ₁ ⊢ C)
    → ⊗l-1 (letI Δ₀ Δ₁ f g) ≡ letI (B ∷ Δ₀) Δ₁ f (⊗l-1 g)
  letI-⊗l-1 Δ₀ Δ₁ (uf f) g = letI-⊗l-1 Δ₀ Δ₁ f g 
  letI-⊗l-1 Δ₀ Δ₁ Ir g = refl
  letI-⊗l-1 {T} Δ₀ Δ₁ (Ic Γ Δ f) g = cong (Ic (_ ∷ Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁)) (letI-⊗l-1 Δ₀ Δ₁ f g)
  letI-⊗l-1 {T} Δ₀ Δ₁ (⊗c Γ Δ cJ cJ' f) g = cong (⊗c (_ ∷ Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁) cJ cJ') (letI-⊗l-1 Δ₀ Δ₁ f g)
  letI-⊗l-1 Δ₀ Δ₁ ax g = refl
  letI-⊗l-1 {T}{Γ} Δ₀ Δ₁ (Il f) g = cong (Ic (_ ∷ Δ₀) (Γ ++ Δ₁)) (letI-⊗l-1 Δ₀ Δ₁ f g)
  letI-⊗l-1 {T}{Γ} Δ₀ Δ₁ (⊗l f) g = cong (⊗c (_ ∷ Δ₀) (Γ ++ Δ₁) _ _) (letI-⊗l-1 Δ₀ Δ₁ f g)


abstract
  mutual
    ccut-⊗l-1 : ∀{T}{Γ Δ}{A B C D} Δ₀ {Δ'}
      → (f : T ∣ Γ ⊢ C)(g : just (A ⊗ B) ∣ Δ ⊢ D)
      → (r : Δ ≡ Δ₀ ++ C ∷ Δ')
      → ⊗l-1 (ccut Δ₀ f g r) ≡ ccut (B ∷ Δ₀) f (⊗l-1 g) (cong (_∷_ B) r)
    ccut-⊗l-1 Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-⊗l-1 Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') r with cases++ Δ₀ Γ Δ' Δ r
    ccut-⊗l-1 {T}{Γ} {C = C} Δ₀ f (⊗r {Δ = Δ} g g') refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ Δ C =
      cong₂ (⊗r {Γ = _ ∷ Δ₀ ++ asCxt T Γ ++ Γ₀}{Δ}) (ccut-⊗l-1 Δ₀ f g refl) refl
    ccut-⊗l-1 {C = C} ._ {Δ'} f (⊗r {Γ = Γ} g g') refl | inj₂ (Γ₀ , refl , refl)
      rewrite cases++-inj₂ Γ₀ Γ Δ' C = refl
    ccut-⊗l-1 Δ₀ f (⊗l g) r = refl
    ccut-⊗l-1 Δ₀ {Δ'} f (Ic Γ Δ g) r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    ccut-⊗l-1 {T}{Γ} {C = C} Δ₀ {.(Γ₀ ++ I ∷ Δ)} f (Ic .(Δ₀ ++ C ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (I ∷ Δ) C = cong (Ic (_ ∷ Δ₀ ++ asCxt T Γ ++ Γ₀) Δ) (ccut-⊗l-1 Δ₀ f g refl)
    ccut-⊗l-1 .Γ {.Δ} f (Ic Γ Δ g) refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Γ Δ I = letI-⊗l-1 Γ Δ f g
    ccut-⊗l-1 {T}{Γ₁} {C = C} .(Γ ++ I ∷ Γ₀) {Δ'} f (Ic Γ .(Γ₀ ++ C ∷ Δ') g) refl | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀) Γ Δ' C = cong (Ic (_ ∷ Γ) (Γ₀ ++ asCxt T Γ₁ ++ Δ')) (ccut-⊗l-1 (Γ ++ Γ₀) f g refl)
    ccut-⊗l-1 Δ₀ {Δ'} f (⊗c Γ Δ {J}{J'} cJ cJ' g) r with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) r
    ccut-⊗l-1 {T}{Γ} {C = C} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} f (⊗c .(Δ₀ ++ C ∷ Γ₀) Δ {J}{J'} cJ cJ' g) refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Δ) C = cong (⊗c (_ ∷ Δ₀ ++ asCxt T Γ ++ Γ₀) Δ cJ cJ') (ccut-⊗l-1 Δ₀ f g refl)
    ccut-⊗l-1 .Γ {.Δ} f (⊗c Γ Δ {J}{J'} cJ cJ' g) refl | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Γ Δ (J ⊗ J') = let⊗-⊗l-1 Γ Δ f g 
    ccut-⊗l-1 {T}{Γ₁} {C = C} .(Γ ++ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ C ∷ Δ') {J}{J'} cJ cJ' g) refl | inj₂ (._ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ Δ' C = cong (⊗c (_ ∷ Γ) (Γ₀ ++ asCxt T Γ₁ ++ Δ') cJ cJ') (ccut-⊗l-1 (Γ ++ J ∷ J' ∷ Γ₀) f g refl)
  
    let⊗-⊗l-1 : ∀{T}{Γ}{A B C J J'} Δ₀ Δ₁ {cJ : isCl J} {cJ' : isCl J'}
      → (f : T ∣ Γ ⊢ J ⊗ J')(g : just (A ⊗ B) ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
      → ⊗l-1 (let⊗ Δ₀ Δ₁ cJ cJ' f g) ≡ let⊗ (B ∷ Δ₀) Δ₁ cJ cJ' f (⊗l-1 g)
    let⊗-⊗l-1 Δ₀ Δ₁ (uf f) g = let⊗-⊗l-1 Δ₀ Δ₁ f g
    let⊗-⊗l-1 Δ₀ Δ₁ (⊗r f f₁) g =
      trans (ccut-⊗l-1 Δ₀ f (ccut (Δ₀ ++ _ ∷ []) f₁ g refl) refl)
        (cong (λ x → ccut (_ ∷ Δ₀) f x refl) (ccut-⊗l-1 (Δ₀ ++ _ ∷ []) f₁ g refl))
    let⊗-⊗l-1 {T} Δ₀ Δ₁ (Ic Γ Δ f) g = cong (Ic (_ ∷ Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁)) (let⊗-⊗l-1 Δ₀ Δ₁ f g)
    let⊗-⊗l-1 {T} Δ₀ Δ₁ (⊗c Γ Δ cJ₁ cJ'' f) g = cong (⊗c (_ ∷ Δ₀ ++ asCxt T Γ) (Δ ++ Δ₁) cJ₁ cJ'') (let⊗-⊗l-1 Δ₀ Δ₁ f g)
    let⊗-⊗l-1 Δ₀ Δ₁ ax g = refl
    let⊗-⊗l-1 {_}{Γ} Δ₀ Δ₁ (Il f) g = cong (Ic (_ ∷ Δ₀) (Γ ++ Δ₁)) (let⊗-⊗l-1 Δ₀ Δ₁ f g)
    let⊗-⊗l-1 {_}{Γ} Δ₀ Δ₁ (⊗l f) g = cong (⊗c (_ ∷ Δ₀) (Γ ++ Δ₁) _ _) (let⊗-⊗l-1 Δ₀ Δ₁ f g)

-- Lots of permutation laws

abstract
  ⊗l-1-scut⊗r : {Γ : Cxt} → {A B C : Fma}
    → (f : just (A ⊗ B) ∣ Γ ⊢ C)
    → ⊗l-1 f ≡ scut (⊗r ax (uf ax)) f
  ⊗l-1-scut⊗r ax = refl
  ⊗l-1-scut⊗r (⊗r {Γ = Γ} {Δ} f f₁) = cong₂ (⊗r {Γ = _ ∷ Γ}{Δ}) (⊗l-1-scut⊗r f) refl
  ⊗l-1-scut⊗r (⊗l f) = sym (ccut-unit [] f refl)  
  ⊗l-1-scut⊗r (Ic Γ Δ f) = cong (Ic (_ ∷ Γ) Δ) (⊗l-1-scut⊗r f)
  ⊗l-1-scut⊗r (⊗c Γ Δ cJ cJ' f) = cong (⊗c (_ ∷ Γ) Δ cJ cJ') (⊗l-1-scut⊗r f)

  mutual
    letI-[] : {Γ : Cxt} (Δ : Cxt) → {C : Fma}
      → (f : nothing ∣ Γ ⊢ I)(g : nothing ∣ Δ ⊢ C)
      → letI [] Δ f g ≗ scut f (Il g)
    letI-[] Δ₀ (uf f) g = letI-[]-j Δ₀ f g
    letI-[] Δ₀ Ir g = refl
    letI-[] Δ₀ (Ic Γ Δ f) g = Ic Γ (Δ ++ Δ₀) (letI-[] Δ₀ f g )
    letI-[] Δ₀ (⊗c Γ Δ cJ cJ' f) g = ⊗c Γ (Δ ++ Δ₀) _ _ (letI-[] Δ₀ f g )
  
    letI-[]-j : {Γ : Cxt} (Δ : Cxt) → {A C : Fma}
      → (f : just A ∣ Γ ⊢ I)(g : nothing ∣ Δ ⊢ C)
      → letI [] Δ f g ≗ uf (scut f (Il g))
    letI-[]-j Δ ax g = ~ ufIc1
    letI-[]-j Δ (Il f) g = (~ ufIc1) ∙ uf (Il (letI-[] Δ f g))
    letI-[]-j Δ (⊗l {Γ = Γ} f) g = ⊗c [] (Γ ++ Δ) _ _ (letI-[]-j Δ f g) ∙ (~ uf⊗c1)
    letI-[]-j Δ (Ic Γ Δ₁ f) g = Ic (_ ∷ Γ) (Δ₁ ++ Δ) (letI-[]-j Δ f g) ∙ (~ ufIc2)
    letI-[]-j Δ (⊗c Γ Δ₁ cJ cJ' f) g = ⊗c (_ ∷ Γ) (Δ₁ ++ Δ) _ _ (letI-[]-j Δ f g) ∙ (~ uf⊗c2)

  mutual
    let⊗-[] : {Γ : Cxt} (Δ : Cxt) → {C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'}
      → (f : nothing ∣ Γ ⊢ J ⊗ J')(g : just J ∣ J' ∷ Δ ⊢ C)
      → let⊗ [] Δ cJ cJ' f (uf g) ≗ scut f (⊗l g)
    let⊗-[] Δ₀ (uf f) g = let⊗-[]-j Δ₀ f g
    let⊗-[] Δ₀ (⊗r f f₁) g = refl
    let⊗-[] Δ₀ (Ic Γ Δ f) g = Ic Γ (Δ ++ Δ₀) (let⊗-[] Δ₀ f g )
    let⊗-[] Δ₀ (⊗c Γ Δ cJ cJ' f) g = ⊗c Γ (Δ ++ Δ₀) _ _ (let⊗-[] Δ₀ f g )
  
    let⊗-[]-j : {Γ : Cxt} (Δ : Cxt) → {A C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'}
      → (f : just A ∣ Γ ⊢ J ⊗ J')(g : just J ∣ J' ∷ Δ ⊢ C)
      → let⊗ [] Δ cJ cJ' f (uf g) ≗ uf (scut f (⊗l g))
    let⊗-[]-j Δ ax g = ~ uf⊗c1
    let⊗-[]-j Δ (⊗r f f₁) g = refl
    let⊗-[]-j Δ (Il f) g = (~ ufIc1) ∙ uf (Il (let⊗-[] Δ f g))
    let⊗-[]-j Δ (⊗l  {Γ = Γ} f) g = ⊗c [] (Γ ++ Δ) _ _ (let⊗-[]-j Δ f g) ∙ (~ uf⊗c1)
    let⊗-[]-j Δ (Ic Γ Δ₁ f) g = Ic (_ ∷ Γ) (Δ₁ ++ Δ) (let⊗-[]-j Δ f g) ∙ (~ ufIc2)
    let⊗-[]-j Δ (⊗c Γ Δ₁ cJ cJ' f) g = ⊗c (_ ∷ Γ) (Δ₁ ++ Δ) _ _ (let⊗-[]-j Δ f g) ∙ (~ uf⊗c2)

  letI-uf : {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {A C : Fma} → 
               (f : S ∣ Γ ⊢ I)(g : just A ∣ Δ₁ ++ Δ₂ ⊢ C)  →
               letI (A ∷ Δ₁) Δ₂ f (uf g) ≗ uf (letI Δ₁ Δ₂ f g)
  letI-uf Δ₁ Δ₂ ax g = ~ ufIc2
  letI-uf Δ₁ Δ₂ (uf f) g = letI-uf Δ₁ Δ₂ f g
  letI-uf Δ₁ Δ₂ Ir g = refl
  letI-uf {Γ = Γ} Δ₁ Δ₂ (Il f) g = Ic (_ ∷ Δ₁) (Γ ++ Δ₂) (letI-uf Δ₁ Δ₂ f g) ∙ (~ ufIc2)
  letI-uf {Γ = Γ} Δ₁ Δ₂ (⊗l f) g = ⊗c (_ ∷ Δ₁) (Γ ++ Δ₂) _ _ (letI-uf Δ₁ Δ₂ f g) ∙ (~ uf⊗c2)
  letI-uf {S} Δ₁ Δ₂ (Ic Γ Δ f) g = Ic (_ ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (letI-uf Δ₁ Δ₂ f g) ∙ (~ ufIc2 {Γ = Δ₁ ++ asCxt S Γ})
  letI-uf {S} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (_ ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _ _ (letI-uf Δ₁ Δ₂ f g) ∙ (~ uf⊗c2 {Γ = Δ₁ ++ asCxt S Γ})

  letI-Il : {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {C : Fma} → 
               (f : S ∣ Γ ⊢ I)(g : nothing ∣ Δ₁ ++ Δ₂ ⊢ C)  →
                 letI Δ₁ Δ₂ f (Il g) ≗ Il (letI Δ₁ Δ₂ f g)
  letI-Il Δ₁ Δ₂ ax g = ~ IlIc
  letI-Il Δ₁ Δ₂ (uf f) g = letI-Il Δ₁ Δ₂ f g
  letI-Il Δ₁ Δ₂ Ir g = refl
  letI-Il {Γ = Γ} Δ₁ Δ₂ (Il f) g = Ic Δ₁ (Γ ++ Δ₂) (letI-Il Δ₁ Δ₂ f g) ∙ (~ IlIc)
  letI-Il {Γ = Γ} Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₁ (Γ ++ Δ₂) _ _ (letI-Il Δ₁ Δ₂ f g) ∙ (~ Il⊗c)
  letI-Il {S} Δ₁ Δ₂ (Ic Γ Δ f) g =  Ic (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (letI-Il Δ₁ Δ₂ f g) ∙ (~ IlIc {Γ = Δ₁ ++ asCxt S Γ}) 
  letI-Il {S} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _ _ (letI-Il Δ₁ Δ₂ f g) ∙ (~ Il⊗c {Γ = Δ₁ ++ asCxt S Γ}) 
  
  letI-⊗l : {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {A B C : Fma} → 
               (f : S ∣ Γ ⊢ I)(g : just A ∣ B ∷ Δ₁ ++ Δ₂ ⊢ C)  →
              letI Δ₁ Δ₂ f (⊗l g) ≗ ⊗l (letI (B ∷ Δ₁) Δ₂ f g)
  letI-⊗l Δ₁ Δ₂ ax g = ~ ⊗lIc
  letI-⊗l Δ₁ Δ₂ (uf f) g = letI-⊗l Δ₁ Δ₂ f g
  letI-⊗l Δ₁ Δ₂ Ir g = refl
  letI-⊗l {Γ = Γ} Δ₁ Δ₂ (Il f) g = Ic Δ₁ (Γ ++ Δ₂) (letI-⊗l Δ₁ Δ₂ f g) ∙ (~ ⊗lIc)
  letI-⊗l {Γ = Γ} Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₁ (Γ ++ Δ₂) _ _ (letI-⊗l Δ₁ Δ₂ f g) ∙ (~ ⊗l⊗c)
  letI-⊗l {S} Δ₁ Δ₂ (Ic Γ Δ f) g =  Ic (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (letI-⊗l Δ₁ Δ₂ f g) ∙ (~ ⊗lIc {Γ = Δ₁ ++ asCxt S Γ}) 
  letI-⊗l {S} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _ _ (letI-⊗l Δ₁ Δ₂ f g) ∙ (~ ⊗l⊗c {Γ = Δ₁ ++ asCxt S Γ}) 

  
  letI-⊗r1 : {S T : Stp} → {Γ Δ : Cxt} (Δ₁ Δ₂ : Cxt) → {A B : Fma} → 
               (f : S ∣ Γ ⊢ I)(g : T ∣ Δ₁ ++ Δ₂ ⊢ A)(g' : nothing ∣ Δ ⊢ B)  →
              letI Δ₁ (Δ₂ ++ Δ) f (⊗r g g') ≗ ⊗r (letI Δ₁ Δ₂ f g) g'
  letI-⊗r1 Δ₁ Δ₂ ax g g' = ~ ⊗rIc1
  letI-⊗r1 Δ₁ Δ₂ (uf f) g g' = letI-⊗r1 Δ₁ Δ₂ f g g'
  letI-⊗r1 Δ₁ Δ₂ Ir g g' = refl
  letI-⊗r1 {Γ = Γ}{Δ} Δ₁ Δ₂ (Il f) g g' = Ic Δ₁ (Γ ++ Δ₂ ++ Δ) (letI-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗rIc1)
  letI-⊗r1 {Γ = Γ}{Δ} Δ₁ Δ₂ (⊗l f) g g' = ⊗c Δ₁ (Γ ++ Δ₂ ++ Δ) _ _ (letI-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c1)
  letI-⊗r1 {S} {Δ = Δ₃} Δ₁ Δ₂ (Ic Γ Δ f) g g' = Ic (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂ ++ Δ₃) (letI-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗rIc1 {Γ = Δ₁ ++ asCxt S Γ})
  letI-⊗r1 {S} {Δ = Δ₃} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g g' = ⊗c (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂ ++ Δ₃) _ _ (letI-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c1 {Γ = Δ₁ ++ asCxt S Γ})
  
  letI-⊗r2 : {S T : Stp} → {Γ Δ : Cxt} (Δ₁ Δ₂ : Cxt) → {A B : Fma} → 
               (f : S ∣ Γ ⊢ I)(g : T ∣ Δ ⊢ A)(g' : nothing ∣ Δ₁ ++ Δ₂ ⊢ B)  →
              letI (Δ ++ Δ₁) Δ₂ f (⊗r g g') ≗ ⊗r g (letI Δ₁ Δ₂ f g')
  letI-⊗r2 Δ₁ Δ₂ ax g g' = ~ ⊗rIc2
  letI-⊗r2 Δ₁ Δ₂ (uf f) g g' = letI-⊗r2 Δ₁ Δ₂ f g g'
  letI-⊗r2 Δ₁ Δ₂ Ir g g' = refl
  letI-⊗r2 {Γ = Γ}{Δ} Δ₁ Δ₂ (Il f) g g' = Ic (Δ ++ Δ₁) (Γ ++ Δ₂) (letI-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗rIc2)
  letI-⊗r2 {Γ = Γ}{Δ} Δ₁ Δ₂ (⊗l f) g g' = ⊗c (Δ ++ Δ₁) (Γ ++ Δ₂) _ _ (letI-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c2)
  letI-⊗r2 {S}{Δ = Δ₃} Δ₁ Δ₂ (Ic Γ Δ f) g g' = Ic (Δ₃ ++ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (letI-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗rIc2 {Γ = Δ₃}{Δ₁ ++ asCxt S Γ})
  letI-⊗r2 {S}{Δ = Δ₃} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g g' = ⊗c (Δ₃ ++ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _ _ (letI-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c2 {Γ = Δ₃}{Δ₁ ++ asCxt S Γ})
  
  letI-Ic1 : {S T : Stp} → {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) → {C : Fma} → 
               (f : S ∣ Γ ⊢ I)(g : T ∣ Δ₀ ++ Δ₁ ++ Δ₂ ⊢ C)  →
              letI Δ₀ (Δ₁ ++ I ∷ Δ₂) f (Ic (Δ₀ ++ Δ₁) Δ₂ g)
                ≗ Ic (Δ₀ ++ asCxt S Γ ++ Δ₁) Δ₂ (letI Δ₀ (Δ₁ ++ Δ₂) f g)
  letI-Ic1 Δ₀ Δ₁ Δ₂ ax g = IcIc
  letI-Ic1 Δ₀ Δ₁ Δ₂ (uf f) g = letI-Ic1 Δ₀ Δ₁ Δ₂ f g
  letI-Ic1 Δ₀ Δ₁ Δ₂ Ir g = refl
  letI-Ic1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = Ic Δ₀ (Γ ++ Δ₁ ++ I ∷ Δ₂) (letI-Ic1 Δ₀ Δ₁ Δ₂ f g) ∙ IcIc {Γ = Δ₀}{Γ ++ Δ₁}
  letI-Ic1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₀ (Γ ++ Δ₁ ++ I ∷ Δ₂) _ _ (letI-Ic1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗cIc {Γ = Δ₀}{Γ ++ Δ₁}
  letI-Ic1 {S} Δ₀ Δ₁ Δ₂ (Ic Γ Δ f) g =  Ic (Δ₀ ++ asCxt S Γ) (Δ ++ Δ₁ ++ I ∷ Δ₂) (letI-Ic1 Δ₀ Δ₁ Δ₂ f g) ∙ IcIc {Γ = Δ₀ ++ asCxt S Γ}{Δ ++ Δ₁}
  letI-Ic1 {S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₀ ++ asCxt S Γ) (Δ ++ Δ₁ ++ I ∷ Δ₂) _ _ (letI-Ic1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗cIc {Γ = Δ₀ ++ asCxt S Γ}{Δ ++ Δ₁}

  letI-⊗c1 : {S T : Stp} → {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) → {C J J' : Fma} {cJ : isCl J} {cJ' : isCl J'} → 
               (f : S ∣ Γ ⊢ I)(g : T ∣ Δ₀ ++ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)  →
              letI Δ₀ (Δ₁ ++ J ⊗ J' ∷ Δ₂) f (⊗c (Δ₀ ++ Δ₁) Δ₂ cJ cJ' g)
                ≗ ⊗c (Δ₀ ++ asCxt S Γ ++ Δ₁) Δ₂ cJ cJ' (letI Δ₀ (Δ₁ ++ J ∷ J' ∷ Δ₂) f g)
  letI-⊗c1 Δ₀ Δ₁ Δ₂ ax g = Ic⊗c
  letI-⊗c1 Δ₀ Δ₁ Δ₂ (uf f) g = letI-⊗c1 Δ₀ Δ₁ Δ₂ f g
  letI-⊗c1 Δ₀ Δ₁ Δ₂ Ir g = refl
  letI-⊗c1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = Ic Δ₀ (Γ ++ Δ₁ ++ _ ∷ Δ₂) (letI-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ Ic⊗c {Γ = Δ₀}{Γ ++ Δ₁}
  letI-⊗c1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₀ (Γ ++ Δ₁ ++ _ ∷ Δ₂) _ _ (letI-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗c⊗c {Γ = Δ₀}{Γ ++ Δ₁}
  letI-⊗c1 {S} Δ₀ Δ₁ Δ₂ (Ic Γ Δ f) g =  Ic (Δ₀ ++ asCxt S Γ) (Δ ++ Δ₁ ++ _ ∷ Δ₂) (letI-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ Ic⊗c {Γ = Δ₀ ++ asCxt S Γ}{Δ ++ Δ₁}
  letI-⊗c1 {S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₀ ++ asCxt S Γ) (Δ ++ Δ₁ ++ _ ∷ Δ₂) _ _ (letI-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗c⊗c {Γ = Δ₀ ++ asCxt S Γ}{Δ ++ Δ₁}


  letI-Ic2 : {S T : Stp} → {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) → {C : Fma} → 
               (f : S ∣ Γ ⊢ I)(g : T ∣ Δ₀ ++ Δ₁ ++ Δ₂ ⊢ C)  →
              letI (Δ₀ ++ I ∷ Δ₁) Δ₂ f (Ic Δ₀ (Δ₁ ++ Δ₂) g)
                ≗ Ic Δ₀ (Δ₁ ++ asCxt S Γ ++ Δ₂) (letI (Δ₀ ++ Δ₁) Δ₂ f g)
  letI-Ic2 Δ₀ Δ₁ Δ₂ ax g = ~ IcIc
  letI-Ic2 Δ₀ Δ₁ Δ₂ (uf f) g = letI-Ic2 Δ₀ Δ₁ Δ₂ f g
  letI-Ic2 Δ₀ Δ₁ Δ₂ Ir g = refl
  letI-Ic2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = Ic (Δ₀ ++ I ∷ Δ₁) (Γ ++ Δ₂) (letI-Ic2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ IcIc
  letI-Ic2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c (Δ₀ ++ I ∷ Δ₁) (Γ ++ Δ₂) _ _ (letI-Ic2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ Ic⊗c
  letI-Ic2 {S} Δ₀ Δ₁ Δ₂ (Ic Γ Δ f) g = Ic (Δ₀ ++ I ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (letI-Ic2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ IcIc {Γ = Δ₀}{Δ₁ ++ asCxt S Γ}
  letI-Ic2 {S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₀ ++ I ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _  _ (letI-Ic2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ Ic⊗c {Γ = Δ₀}{Δ₁ ++ asCxt S Γ}
  
  
  letI-⊗c2 : {S T : Stp} → {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) → {C J J' : Fma} {cJ : isCl J} {cJ' : isCl J'} → 
               (f : S ∣ Γ ⊢ I)(g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ++ Δ₂ ⊢ C)  →
              letI (Δ₀ ++ J ⊗ J' ∷ Δ₁) Δ₂ f (⊗c Δ₀ (Δ₁ ++ Δ₂) cJ cJ' g)
                ≗ ⊗c Δ₀ (Δ₁ ++ asCxt S Γ ++ Δ₂) cJ cJ' (letI (Δ₀ ++ J ∷ J' ∷ Δ₁) Δ₂ f g)
  letI-⊗c2 Δ₀ Δ₁ Δ₂ ax g = ~ ⊗cIc
  letI-⊗c2 Δ₀ Δ₁ Δ₂ (uf f) g = letI-⊗c2 Δ₀ Δ₁ Δ₂ f g
  letI-⊗c2 Δ₀ Δ₁ Δ₂ Ir g = refl
  letI-⊗c2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = Ic (Δ₀ ++ _ ∷ Δ₁) (Γ ++ Δ₂) (letI-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗cIc
  letI-⊗c2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c (Δ₀ ++ _ ∷ Δ₁) (Γ ++ Δ₂) _ _ (letI-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗c⊗c
  letI-⊗c2 {S} Δ₀ Δ₁ Δ₂ (Ic Γ Δ f) g = Ic (Δ₀ ++ _ ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (letI-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗cIc {Γ = Δ₀}{Δ₁ ++ asCxt S Γ}
  letI-⊗c2 {S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₀ ++ _ ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _  _ (letI-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗c⊗c {Γ = Δ₀}{Δ₁ ++ asCxt S Γ}

  
  ccut-Ic : {S T : Stp} → {Δ : Cxt} → (Δ₀ Γ₁ Γ₂ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
               (f : S ∣ Γ₁ ++ Γ₂ ⊢ A)(g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
              ccut Δ₀ (Ic Γ₁ Γ₂ f) g r ≗ Ic (Δ₀ ++ asCxt S Γ₁) (Γ₂ ++ Δ') (ccut Δ₀ f g r)
  ccut-Ic Δ₀ Γ₁ Γ₂ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-Ic Δ₀ Γ₁ Γ₂ f (uf g) r with cases∷ Δ₀ r
  ccut-Ic {just A'} .[] Γ₁ Γ₂ f (uf g) refl | inj₁ (refl , refl , refl) = ufIc2
  ccut-Ic {nothing} .[] Γ₁ Γ₂ f (uf g) refl | inj₁ (refl , refl , refl) = refl
  ccut-Ic {S} .(_ ∷ Γ₀) Γ₁ Γ₂ {Δ'} f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
    uf (ccut-Ic Γ₀ Γ₁ Γ₂ f g refl) ∙ ufIc2 {Γ = Γ₀ ++ asCxt S Γ₁}
  ccut-Ic Δ₀ Γ₁ Γ₂ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-Ic Δ₀ Γ₁ Γ₂ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
  ccut-Ic {S} Δ₀ Γ₁ Γ₂ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) r | inj₁ (Γ₀ , refl , refl) =
    ⊗r (ccut-Ic Δ₀ Γ₁ Γ₂ f g refl) refl ∙ ⊗rIc1 {Γ = Δ₀ ++ asCxt S Γ₁}
  ccut-Ic {S} .(Γ ++ Γ₀) Γ₁ Γ₂ {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) r | inj₂ (Γ₀ , refl , refl) =
    ⊗r refl (ccut-Ic Γ₀ Γ₁ Γ₂ f g₁ refl) ∙ ⊗rIc2 {Δ = Γ₀ ++ asCxt S Γ₁}
  ccut-Ic {S} Δ₀ Γ₁ Γ₂ f (Il g) refl =
    Il (ccut-Ic Δ₀ Γ₁ Γ₂ f g refl) ∙ IlIc {Γ = Δ₀ ++ asCxt S Γ₁}
  ccut-Ic {S} Δ₀ Γ₁ Γ₂ f (⊗l g) refl = 
    ⊗l (ccut-Ic (_ ∷ Δ₀) Γ₁ Γ₂ f g refl) ∙ ⊗lIc {Γ = Δ₀ ++ asCxt S Γ₁}
  ccut-Ic Δ₀ Γ₁ Γ₂ {Δ'} f (Ic Γ Δ g) r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
  ccut-Ic {S} Δ₀ Γ₁ Γ₂ {.(Γ₀ ++ I ∷ Δ)} f (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
    Ic (Δ₀ ++ asCxt S Γ₁ ++ I ∷ Γ₂ ++ Γ₀) Δ (ccut-Ic Δ₀ Γ₁ Γ₂ f g refl)
    ∙ (~ IcIc {Γ = Δ₀ ++ asCxt S Γ₁}{Γ₂ ++ Γ₀}{Δ})
  ccut-Ic .Γ Γ₁ Γ₂ {.Δ} f (Ic Γ Δ g) refl | inj₂ ([] , refl , refl) = refl
  ccut-Ic {S} .(Γ ++ I ∷ Γ₀) Γ₁ Γ₂ {Δ'} f (Ic Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.I ∷ Γ₀ , refl , refl) =
    Ic Γ (Γ₀ ++ asCxt S Γ₁ ++ I ∷ Γ₂ ++ Δ') (ccut-Ic (Γ ++ Γ₀) Γ₁ Γ₂ f g refl)
    ∙ IcIc {Γ = Γ}{Γ₀ ++ asCxt S Γ₁}
  ccut-Ic Δ₀ Γ₁ Γ₂ {Δ'} f (⊗c Γ Δ cJ cJ' g) r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
  ccut-Ic {S} Δ₀ Γ₁ Γ₂ {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ cJ cJ' g) refl | inj₁ (Γ₀ , refl , refl) =
    ⊗c (Δ₀ ++ asCxt S Γ₁ ++ I ∷ Γ₂ ++ Γ₀) Δ cJ cJ' (ccut-Ic Δ₀ Γ₁ Γ₂ f g refl)
    ∙ (~ Ic⊗c {Γ = Δ₀ ++ asCxt S Γ₁}{Γ₂ ++ Γ₀}{Δ})
  ccut-Ic .Γ Γ₁ Γ₂ {.Δ} f (⊗c Γ Δ cJ cJ' g) refl | inj₂ ([] , refl , refl) = refl
  ccut-Ic {S} .(Γ ++ _ ⊗ _ ∷ Γ₀) Γ₁ Γ₂ {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') cJ cJ' g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    ⊗c Γ (Γ₀ ++ asCxt S Γ₁ ++ I ∷ Γ₂ ++ Δ') cJ cJ' (ccut-Ic (Γ ++ _ ∷ _ ∷ Γ₀) Γ₁ Γ₂ f g refl)
    ∙ ⊗cIc {Γ = Γ}{Γ₀ ++ asCxt S Γ₁}
  
  scut-Ic : {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {A C : Fma} → 
              (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ₁ ++ Δ₂ ⊢ C) →
              scut f (Ic Δ₁ Δ₂ g) ≗ Ic (Γ ++ Δ₁) Δ₂ (scut f g)
  scut-Ic Δ₁ Δ₂ ax g = refl
  scut-Ic Δ₁ Δ₂ (uf {Γ} f) g =
    uf (scut-Ic Δ₁ Δ₂ f g) ∙ ufIc2 {Γ = Γ ++ Δ₁}{Δ₂}
  scut-Ic Δ₁ Δ₂ Ir g = refl
  scut-Ic Δ₁ Δ₂ (⊗r f f₁) g = refl
  scut-Ic {Γ = Γ} Δ₁ Δ₂ (Il f) g =
    Il (scut-Ic Δ₁ Δ₂ f g) ∙ IlIc {Γ = Γ ++ Δ₁}{Δ₂}
  scut-Ic {Γ = Γ} Δ₁ Δ₂ (⊗l f) g =
    ⊗l (scut-Ic Δ₁ Δ₂ f g) ∙ ⊗lIc {Γ = Γ ++ Δ₁}{Δ₂}
  scut-Ic Δ₁ Δ₂ (Ic Γ Δ f) g =
    Ic Γ (Δ ++ Δ₁ ++ I ∷ Δ₂) (scut-Ic Δ₁ Δ₂ f g)
    ∙ IcIc {Γ = Γ}{Δ ++ Δ₁}{Δ₂}
  scut-Ic Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g =
    ⊗c Γ (Δ ++ Δ₁ ++ _ ∷ Δ₂) cJ cJ' (scut-Ic Δ₁ Δ₂ f g)
    ∙ ⊗cIc {Γ = Γ}{Δ ++ Δ₁}{Δ₂}
  
  ccut-⊗c : {S T : Stp} → {Δ : Cxt} → (Δ₀ Γ₁ Γ₂ : Cxt) → {Δ' : Cxt} →  {A C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'} → 
               (f : S ∣ Γ₁ ++ J ∷ J' ∷ Γ₂ ⊢ A)(g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
              ccut Δ₀ (⊗c Γ₁ Γ₂ cJ cJ' f) g r ≗ ⊗c (Δ₀ ++ asCxt S Γ₁) (Γ₂ ++ Δ') cJ cJ' (ccut Δ₀ f g r)
  ccut-⊗c Δ₀ Γ₁ Γ₂ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-⊗c Δ₀ Γ₁ Γ₂ f (uf g) r with cases∷ Δ₀ r
  ccut-⊗c {just A'} .[] Γ₁ Γ₂ f (uf g) refl | inj₁ (refl , refl , refl) = uf⊗c2
  ccut-⊗c {nothing} .[] Γ₁ Γ₂ f (uf g) refl | inj₁ (refl , refl , refl) = refl
  ccut-⊗c {S} .(_ ∷ Γ₀) Γ₁ Γ₂ {Δ'} f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
    uf (ccut-⊗c Γ₀ Γ₁ Γ₂ f g refl) ∙ uf⊗c2 {Γ = Γ₀ ++ asCxt S Γ₁}
  ccut-⊗c Δ₀ Γ₁ Γ₂ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-⊗c Δ₀ Γ₁ Γ₂ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
  ccut-⊗c {S} Δ₀ Γ₁ Γ₂ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) r | inj₁ (Γ₀ , refl , refl) =
    ⊗r (ccut-⊗c Δ₀ Γ₁ Γ₂ f g refl) refl ∙ ⊗r⊗c1 {Γ = Δ₀ ++ asCxt S Γ₁}
  ccut-⊗c {S} .(Γ ++ Γ₀) Γ₁ Γ₂ {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) r | inj₂ (Γ₀ , refl , refl) =
    ⊗r refl (ccut-⊗c Γ₀ Γ₁ Γ₂ f g₁ refl) ∙ ⊗r⊗c2 {Δ = Γ₀ ++ asCxt S Γ₁}
  ccut-⊗c {S} Δ₀ Γ₁ Γ₂ f (Il g) refl =
    Il (ccut-⊗c Δ₀ Γ₁ Γ₂ f g refl) ∙ Il⊗c {Γ = Δ₀ ++ asCxt S Γ₁}
  ccut-⊗c {S} Δ₀ Γ₁ Γ₂ f (⊗l g) refl = 
    ⊗l (ccut-⊗c (_ ∷ Δ₀) Γ₁ Γ₂ f g refl) ∙ ⊗l⊗c {Γ = Δ₀ ++ asCxt S Γ₁}
  ccut-⊗c Δ₀ Γ₁ Γ₂ {Δ'} f (Ic Γ Δ g) r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
  ccut-⊗c {S} Δ₀ Γ₁ Γ₂ {.(Γ₀ ++ I ∷ Δ)} f (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
    Ic (Δ₀ ++ asCxt S Γ₁ ++ _ ∷ Γ₂ ++ Γ₀) Δ (ccut-⊗c Δ₀ Γ₁ Γ₂ f g refl)
    ∙ (~ ⊗cIc {Γ = Δ₀ ++ asCxt S Γ₁}{Γ₂ ++ Γ₀}{Δ})
  ccut-⊗c .Γ Γ₁ Γ₂ {.Δ} f (Ic Γ Δ g) refl | inj₂ ([] , refl , refl) = refl
  ccut-⊗c {S} .(Γ ++ _ ∷ Γ₀) Γ₁ Γ₂ {Δ'} f (Ic Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.I ∷ Γ₀ , refl , refl) =
    Ic Γ (Γ₀ ++ asCxt S Γ₁ ++ _ ∷ Γ₂ ++ Δ') (ccut-⊗c (Γ ++ Γ₀) Γ₁ Γ₂ f g refl)
    ∙ Ic⊗c {Γ = Γ}{Γ₀ ++ asCxt S Γ₁}
  ccut-⊗c Δ₀ Γ₁ Γ₂ {Δ'} f (⊗c Γ Δ cJ cJ' g) r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
  ccut-⊗c {S} Δ₀ Γ₁ Γ₂ {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ cJ cJ' g) refl | inj₁ (Γ₀ , refl , refl) =
    ⊗c (Δ₀ ++ asCxt S Γ₁ ++ _ ∷ Γ₂ ++ Γ₀) Δ cJ cJ' (ccut-⊗c Δ₀ Γ₁ Γ₂ f g refl)
    ∙ (~ ⊗c⊗c {Γ = Δ₀ ++ asCxt S Γ₁}{Γ₂ ++ Γ₀}{Δ})
  ccut-⊗c .Γ Γ₁ Γ₂ {.Δ} f (⊗c Γ Δ cJ cJ' g) refl | inj₂ ([] , refl , refl) = refl
  ccut-⊗c {S} .(Γ ++ _ ⊗ _ ∷ Γ₀) Γ₁ Γ₂ {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') cJ cJ' g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    ⊗c Γ (Γ₀ ++ asCxt S Γ₁ ++ _ ∷ Γ₂ ++ Δ') cJ cJ' (ccut-⊗c (Γ ++ _ ∷ _ ∷ Γ₀) Γ₁ Γ₂ f g refl)
    ∙ ⊗c⊗c {Γ = Γ}{Γ₀ ++ asCxt S Γ₁}
  
  scut-⊗c : {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {A C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'} → 
              (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C) →
              scut f (⊗c Δ₁ Δ₂ cJ cJ' g) ≗ ⊗c (Γ ++ Δ₁) Δ₂ cJ cJ' (scut f g)
  scut-⊗c Δ₁ Δ₂ ax g = refl
  scut-⊗c Δ₁ Δ₂ (uf {Γ} f) g =
    uf (scut-⊗c Δ₁ Δ₂ f g) ∙ uf⊗c2 {Γ = Γ ++ Δ₁}{Δ₂}
  scut-⊗c Δ₁ Δ₂ Ir g = refl
  scut-⊗c Δ₁ Δ₂ (⊗r f f₁) g = refl
  scut-⊗c {Γ = Γ} Δ₁ Δ₂ (Il f) g =
    Il (scut-⊗c Δ₁ Δ₂ f g) ∙ Il⊗c {Γ = Γ ++ Δ₁}{Δ₂}
  scut-⊗c {Γ = Γ} Δ₁ Δ₂ (⊗l f) g =
    ⊗l (scut-⊗c Δ₁ Δ₂ f g) ∙ ⊗l⊗c {Γ = Γ ++ Δ₁}{Δ₂}
  scut-⊗c Δ₁ Δ₂ (Ic Γ Δ f) g =
    Ic Γ (Δ ++ Δ₁ ++ _ ∷ Δ₂) (scut-⊗c Δ₁ Δ₂ f g)
    ∙ Ic⊗c {Γ = Γ}{Δ ++ Δ₁}{Δ₂}
  scut-⊗c Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g =
    ⊗c Γ (Δ ++ Δ₁ ++ _ ∷ Δ₂) cJ cJ' (scut-⊗c Δ₁ Δ₂ f g)
    ∙ ⊗c⊗c {Γ = Γ}{Δ ++ Δ₁}{Δ₂}
  
  
  cong-letI1 : {S T : Stp} {Γ : Cxt} → (Δ₀ Δ' : Cxt) → {C : Fma} → 
               {f f' : S ∣ Γ ⊢ I}(g : T ∣ Δ₀ ++ Δ' ⊢ C)  → 
               f ≗ f' → letI Δ₀ Δ' f g ≗ letI Δ₀ Δ' f' g
  cong-letI1 Δ₀ Δ' g refl = refl
  cong-letI1 Δ₀ Δ' g (~ p) = ~ cong-letI1 Δ₀ Δ' g p
  cong-letI1 Δ₀ Δ' g (p ∙ p₁) = cong-letI1 Δ₀ Δ' g p ∙ cong-letI1 Δ₀ Δ' g p₁
  cong-letI1 Δ₀ Δ' g (uf p) = cong-letI1 Δ₀ Δ' g p
  cong-letI1 {Γ = Γ} Δ₀ Δ' g (⊗l {g = g'} p) = ⊗c Δ₀ (Γ ++ Δ') _ _ (cong-letI1 Δ₀ Δ' g p) ∙
    ≡-to-≗ (cong₂ (λ x y → ⊗c Δ₀ (Γ ++ Δ') x y (letI Δ₀ Δ' g' g)) (uniq-cl _ _) (uniq-cl _ _))
  cong-letI1 {Γ = Γ} Δ₀ Δ' g (Il p) = Ic Δ₀ (Γ ++ Δ') (cong-letI1 Δ₀ Δ' g p)
  cong-letI1 Δ₀ Δ' g axI = refl
  cong-letI1 {S} Δ₀ Δ' g (Ic Γ Δ p) = Ic (Δ₀ ++ asCxt S Γ) (Δ ++ Δ') (cong-letI1 {S} Δ₀ Δ' g p)
  cong-letI1 Δ₀ Δ' g ufIc1 = refl
  cong-letI1 {S} Δ₀ Δ' g (IcIc {Γ = Γ} {Δ} {Λ}) = IcIc {Γ = Δ₀ ++ asCxt S Γ}{Δ}{Λ ++ Δ'}
  cong-letI1 {S} Δ₀ Δ' g (⊗cIc {Γ = Γ} {Δ} {Λ}) = ⊗cIc {Γ = Δ₀ ++ asCxt S Γ}{Δ}{Λ ++ Δ'}
  cong-letI1 Δ₀ Δ' g ufIc2 = refl
  cong-letI1 Δ₀ Δ' g IlIc = IcIc
  cong-letI1 Δ₀ Δ' g (⊗lIc {Γ} {Δ} {A} {B} {f = f}) = ⊗cIc {Γ = Δ₀}{Γ}{Δ ++ Δ'} ∙
    Ic (Δ₀ ++ A ⊗ B ∷ Γ) (Δ ++ Δ') (≡-to-≗ (cong₂ (λ x y → ⊗c Δ₀ (Γ ++ Δ ++ Δ') x y (letI Δ₀ Δ' f g)) (uniq-cl _ _) (uniq-cl _ _))) 
  cong-letI1 {S} Δ₀ Δ' g (⊗c Γ Δ _ _ p) = ⊗c (Δ₀ ++ asCxt S Γ) (Δ ++ Δ') _ _ (cong-letI1 {S} Δ₀ Δ' g p)
  cong-letI1 Δ₀ Δ' g (uf⊗c1 {Γ} {f = f}) = ≡-to-≗ (cong₂ (λ x y → ⊗c Δ₀ (Γ ++ Δ') x y (letI Δ₀ Δ' f g)) (uniq-cl _ _) (uniq-cl _ _))
  cong-letI1 {S} Δ₀ Δ' g (Ic⊗c {Γ = Γ} {Δ} {Λ}) = Ic⊗c {Γ = Δ₀ ++ asCxt S Γ}{Δ}{Λ ++ Δ'}
  cong-letI1 {S} Δ₀ Δ' g (⊗c⊗c {Γ = Γ} {Δ} {Λ}) = ⊗c⊗c {Γ = Δ₀ ++ asCxt S Γ}{Δ}{Λ ++ Δ'}
  cong-letI1 Δ₀ Δ' g uf⊗c2 = refl
  cong-letI1 Δ₀ Δ' g Il⊗c = Ic⊗c
  cong-letI1 Δ₀ Δ' g (⊗l⊗c {Γ} {Δ} {A} {B} {f = f}) = ⊗c⊗c {Γ = Δ₀}{Γ}{Δ ++ Δ'} ∙
    ⊗c (Δ₀ ++ A ⊗ B ∷ Γ) (Δ ++ Δ') _ _ (≡-to-≗ (cong₂ (λ x y → ⊗c Δ₀ (Γ ++ _ ∷ _ ∷ Δ ++ Δ') x y (letI Δ₀ Δ' f g)) (uniq-cl _ _) (uniq-cl _ _)))
  
  cong-letI2 : {S T : Stp} {Γ : Cxt} → (Δ₀ Δ' : Cxt) → {C : Fma} → 
               (f : S ∣ Γ ⊢ I){g g' : T ∣ Δ₀ ++ Δ' ⊢ C} → 
               g ≗ g' → letI Δ₀ Δ' f g ≗ letI Δ₀ Δ' f g'
  cong-letI2 Δ₀ Δ' ax p = Ic Δ₀ Δ' p
  cong-letI2 Δ₀ Δ' (uf f) p = cong-letI2 Δ₀ Δ' f p
  cong-letI2 Δ₀ Δ' Ir p = p
  cong-letI2 Δ₀ Δ' (Il {Γ = Γ} f) p = Ic Δ₀ (Γ ++ Δ') (cong-letI2 Δ₀ Δ' f p)
  cong-letI2 Δ₀ Δ' (⊗l {Γ = Γ} f) p = ⊗c Δ₀ (Γ ++ Δ') _ _ (cong-letI2 Δ₀ Δ' f p)
  cong-letI2 {S} Δ₀ Δ' (Ic Γ Δ f) p = Ic (Δ₀ ++ asCxt S Γ) (Δ ++ Δ') (cong-letI2 Δ₀ Δ' f p)
  cong-letI2 {S} Δ₀ Δ' (⊗c Γ Δ cJ cJ' f) p = ⊗c (Δ₀ ++ asCxt S Γ) (Δ ++ Δ') cJ cJ' (cong-letI2 Δ₀ Δ' f p)
  
  
  ccut-ax : {T : Stp}{Γ Δ : Cxt}(Δ₀ : Cxt){A C : Fma}
    → (g : T ∣ Δ ⊢ C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
    → ccut Δ₀ ax g r ≡ subst-cxt r g
  ccut-ax Δ₀ ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ax Δ₀ (uf g) r with cases∷ Δ₀ r
  ccut-ax .[] (uf g) refl | inj₁ (refl , refl , refl) = refl
  ccut-ax .(_ ∷ Γ) (uf g) refl | inj₂ (Γ , refl , refl) = cong uf (ccut-ax Γ g refl)
  ccut-ax Δ₀ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ax {_}{Γ} Δ₀ (⊗r {Γ = Γ'}{Δ} g g') r with cases++ Δ₀ Γ' Γ Δ r
  ccut-ax Δ₀ (⊗r {Γ = Γ}{Δ} g g') refl | inj₁ (Γ₀ , refl , refl) = 
    cong₂ (⊗r {Γ = Γ}{Δ}) (ccut-ax Δ₀ g refl) refl
  ccut-ax ._ (⊗r {Γ = Γ}{Δ} g g') refl | inj₂ (Δ₀ , refl , refl) =
    cong₂ (⊗r {Γ = Γ}) refl (ccut-ax Δ₀ g' refl)
  ccut-ax Δ₀ (Il g) refl = cong Il (ccut-ax Δ₀ g refl)
  ccut-ax Δ₀ (⊗l g) refl = cong ⊗l (ccut-ax (_ ∷ Δ₀) g refl)
  ccut-ax {Γ = Γ₁} Δ₀ (Ic Γ Δ g) r with cases++ Δ₀ Γ Γ₁ (I ∷ Δ) r
  ccut-ax {Γ = .(Γ₀ ++ I ∷ Δ)} Δ₀ (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
    cong (Ic (Δ₀ ++ _ ∷ Γ₀) Δ) (ccut-ax Δ₀ g refl)
  ccut-ax {Γ = .Δ} .Γ (Ic Γ Δ g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ Δ I = refl
  ccut-ax {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) (Ic Γ .(Γ₀ ++ _ ∷ Γ₁) g) refl | inj₂ (_ ∷ Γ₀ , refl , refl) =
    cong (Ic Γ (Γ₀ ++ _ ∷ Γ₁)) (ccut-ax (Γ ++ Γ₀) g refl)
  ccut-ax {Γ = Γ₁} Δ₀ (⊗c Γ Δ cJ cj' g) r with cases++ Δ₀ Γ Γ₁ (_ ⊗ _ ∷ Δ) r
  ccut-ax {Γ = .(Γ₀ ++ _ ⊗ _ ∷ Δ)} Δ₀ (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ cJ cj' g) refl | inj₁ (Γ₀ , refl , refl) =
    cong (⊗c (Δ₀ ++ _ ∷ Γ₀) Δ cJ cj') (ccut-ax Δ₀ g refl)
  ccut-ax {Γ = .Δ} .Γ (⊗c Γ Δ {J = J}{J'} cJ cj' g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ Δ (J ⊗ J') = refl
  ccut-ax {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) (⊗c Γ .(Γ₀ ++ _ ∷ Γ₁) cJ cj' g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    cong (⊗c Γ (Γ₀ ++ _ ∷ Γ₁) cJ cj') (ccut-ax (Γ ++ _ ∷ _ ∷ Γ₀) g refl)
  
  ccut-uf : {S : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' C : Fma} → 
               (f : just A' ∣ Γ ⊢ A)(g : S ∣ Δ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ') → 
          ccut Δ₀ (uf f) g r ≡ ccut Δ₀ f g r
  ccut-uf Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-uf Δ₀ f (uf g) r with cases∷ Δ₀ r
  ccut-uf .[] f (uf g) r | inj₁ (refl , refl , refl) = refl
  ccut-uf .(_ ∷ Γ₀) f (uf g) r | inj₂ (Γ₀ , refl , refl) = cong uf (ccut-uf Γ₀ f g refl)
  ccut-uf Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-uf Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
  ccut-uf {_}{Γ} Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) r | inj₁ (Γ₀ , refl , refl) =
    cong₂ (⊗r {Γ = Δ₀ ++ _ ∷ Γ ++ Γ₀}{Δ}) (ccut-uf Δ₀ f g refl) refl
  ccut-uf {_}{Γ₁} .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) r | inj₂ (Γ₀ , refl , refl) =
    cong (⊗r {Γ = Γ}{Γ₀ ++ _ ∷ Γ₁ ++ Δ'} g) (ccut-uf Γ₀ f g₁ refl)
  ccut-uf Δ₀ f (Il g) r = cong Il (ccut-uf Δ₀ f g r)
  ccut-uf Δ₀ f (⊗l g) refl = cong ⊗l (ccut-uf (_ ∷ Δ₀) f g refl)
  ccut-uf Δ₀ {Δ'} f (Ic Γ Δ g) r with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
  ccut-uf {Γ = Γ} Δ₀ {.(Γ₀ ++ I ∷ Δ)} f (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) r | inj₁ (Γ₀ , refl , refl) =
    cong (Ic (Δ₀ ++ _ ∷ Γ ++ Γ₀) Δ) (ccut-uf Δ₀ f g refl)
  ccut-uf .Γ {.Δ} f (Ic Γ Δ g) refl | inj₂ ([] , refl , refl) = refl
  ccut-uf {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} f (Ic Γ .(Γ₀ ++ _ ∷ Δ') g) r | inj₂ (.I ∷ Γ₀ , refl , refl) =
    cong (Ic Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')) (ccut-uf (Γ ++ Γ₀) f g refl)
  ccut-uf Δ₀ {Δ'} f (⊗c Γ Δ cJ cJ' g) r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
  ccut-uf {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ cJ cJ' g) r | inj₁ (Γ₀ , refl , refl) =
    cong (⊗c (Δ₀ ++ _ ∷ Γ ++ Γ₀) Δ _ _) (ccut-uf Δ₀ f g refl)
  ccut-uf .Γ {.Δ} f (⊗c Γ Δ cJ cJ' g) refl | inj₂ ([] , refl , refl) = refl
  ccut-uf {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') cJ cJ' g) r | inj₂ (_ ∷ Γ₀ , refl , refl) =
    cong (⊗c Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ') cJ cJ') (ccut-uf (Γ ++ _ ∷ _ ∷ Γ₀) f g refl)  
  
  let⊗-uf : {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {A C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'} 
               (f : S ∣ Γ ⊢ J ⊗ J')(g : just A ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)  →
              let⊗ (A ∷ Δ₁) Δ₂ cJ cJ' f (uf g) ≗ uf (let⊗ Δ₁ Δ₂ cJ cJ' f g)
  let⊗-uf Δ₁ Δ₂ ax g = ~ uf⊗c2
  let⊗-uf Δ₁ Δ₂ (uf f) g = let⊗-uf Δ₁ Δ₂ f g
  let⊗-uf Δ₁ Δ₂ (⊗r f f₁) g = refl
  let⊗-uf {Γ = Γ} Δ₁ Δ₂ (Il f) g = Ic (_ ∷ Δ₁) (Γ ++ Δ₂) (let⊗-uf Δ₁ Δ₂ f g) ∙ (~ ufIc2)
  let⊗-uf {Γ = Γ} Δ₁ Δ₂ (⊗l f) g = ⊗c (_ ∷ Δ₁) (Γ ++ Δ₂) _ _ (let⊗-uf Δ₁ Δ₂ f g) ∙ (~ uf⊗c2)
  let⊗-uf {S} Δ₁ Δ₂ (Ic Γ Δ f) g = Ic (_ ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (let⊗-uf Δ₁ Δ₂ f g) ∙ (~ ufIc2 {Γ = Δ₁ ++ asCxt S Γ} )
  let⊗-uf {S} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (_ ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _ _ (let⊗-uf Δ₁ Δ₂ f g) ∙ (~ uf⊗c2 {Γ = Δ₁ ++ asCxt S Γ} )
  
  let⊗-Il : {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'} → 
               (f : S ∣ Γ ⊢ J ⊗ J')(g : nothing ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)  →
              let⊗ Δ₁ Δ₂ cJ cJ' f (Il g) ≗ Il (let⊗ Δ₁ Δ₂ cJ cJ' f g)
  let⊗-Il Δ₁ Δ₂ ax g = ~ Il⊗c
  let⊗-Il Δ₁ Δ₂ (uf f) g = let⊗-Il Δ₁ Δ₂ f g
  let⊗-Il Δ₁ Δ₂ (⊗r f f₁) g = refl
  let⊗-Il {Γ = Γ} Δ₁ Δ₂ (Il f) g = Ic Δ₁ (Γ ++ Δ₂) (let⊗-Il Δ₁ Δ₂ f g) ∙ ~ IlIc
  let⊗-Il {Γ = Γ} Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₁ (Γ ++ Δ₂) _ _ (let⊗-Il Δ₁ Δ₂ f g) ∙ ~ Il⊗c
  let⊗-Il {S} Δ₁ Δ₂ (Ic Γ Δ f) g = Ic (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (let⊗-Il Δ₁ Δ₂ f g) ∙ ~ IlIc {Γ = Δ₁ ++ asCxt S Γ}
  let⊗-Il {S} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _ _ (let⊗-Il Δ₁ Δ₂ f g) ∙ ~ Il⊗c {Γ = Δ₁ ++ asCxt S Γ}
  
  let⊗-⊗l : {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {A B C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'} → 
               (f : S ∣ Γ ⊢ J ⊗ J')(g : just A ∣ B ∷ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)  →
              let⊗ Δ₁ Δ₂ cJ cJ' f (⊗l g) ≗ ⊗l (let⊗ (B ∷ Δ₁) Δ₂ cJ cJ' f g)
  let⊗-⊗l Δ₁ Δ₂ ax g = ~ ⊗l⊗c
  let⊗-⊗l Δ₁ Δ₂ (uf f) g = let⊗-⊗l Δ₁ Δ₂ f g
  let⊗-⊗l Δ₁ Δ₂ (⊗r f f₁) g = refl
  let⊗-⊗l {Γ = Γ} Δ₁ Δ₂ (Il f) g = Ic Δ₁ (Γ ++ Δ₂) (let⊗-⊗l Δ₁ Δ₂ f g) ∙ ~ ⊗lIc
  let⊗-⊗l {Γ = Γ} Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₁ (Γ ++ Δ₂) _ _ (let⊗-⊗l Δ₁ Δ₂ f g) ∙ ~ ⊗l⊗c
  let⊗-⊗l {S} Δ₁ Δ₂ (Ic Γ Δ f) g = Ic (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (let⊗-⊗l Δ₁ Δ₂ f g) ∙ ~ ⊗lIc {Γ = Δ₁ ++ asCxt S Γ}
  let⊗-⊗l {S} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _ _ (let⊗-⊗l Δ₁ Δ₂ f g) ∙ ~ ⊗l⊗c {Γ = Δ₁ ++ asCxt S Γ}
  
  let⊗-⊗r1 : {S T : Stp} → {Γ Δ : Cxt} (Δ₁ Δ₂ : Cxt) → {A B J J' : Fma}{cJ : isCl J}{cJ' : isCl J'} → 
               (f : S ∣ Γ ⊢ J ⊗ J')(g : T ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ A)(g' : nothing ∣ Δ ⊢ B)  →
              let⊗ Δ₁ (Δ₂ ++ Δ) cJ cJ' f (⊗r g g') ≗ ⊗r (let⊗ Δ₁ Δ₂ cJ cJ' f g) g'
  let⊗-⊗r1 Δ₁ Δ₂ ax g g' = ~ ⊗r⊗c1
  let⊗-⊗r1 Δ₁ Δ₂ (uf f) g g' = let⊗-⊗r1 Δ₁ Δ₂ f g g'
  let⊗-⊗r1 {Δ = Δ} Δ₁ Δ₂ {J = J} {J'} (⊗r {Δ = Δ₃} f f₁) g g'
    rewrite cases++-inj₁ (Δ₁ ++ J ∷ []) Δ₂ Δ J' | cases++-inj₁ Δ₁ (Δ₃ ++ Δ₂) Δ J = refl
  let⊗-⊗r1 {Γ = Γ}{Δ} Δ₁ Δ₂ (Il f) g g' = Ic Δ₁ (Γ ++ Δ₂ ++ Δ) (let⊗-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗rIc1)
  let⊗-⊗r1 {Γ = Γ}{Δ} Δ₁ Δ₂ (⊗l f) g g' = ⊗c Δ₁ (Γ ++ Δ₂ ++ Δ) _ _ (let⊗-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c1)
  let⊗-⊗r1 {S} {Δ = Δ₃} Δ₁ Δ₂ (Ic Γ Δ f) g g' = Ic (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂ ++ Δ₃) (let⊗-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗rIc1 {Γ = Δ₁ ++ asCxt S Γ})
  let⊗-⊗r1 {S} {Δ = Δ₃} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g g' = ⊗c (Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂ ++ Δ₃) _ _ (let⊗-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c1 {Γ = Δ₁ ++ asCxt S Γ})


  let⊗-⊗r2 : {S T : Stp} → {Γ Δ : Cxt} (Δ₁ Δ₂ : Cxt) → {A B J J' : Fma}{cJ : isCl J}{cJ' : isCl J'} → 
               (f : S ∣ Γ ⊢ J ⊗ J')(g : T ∣ Δ ⊢ A)(g' : nothing ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ B)  →
              let⊗ (Δ ++ Δ₁) Δ₂ cJ cJ' f (⊗r g g') ≗ ⊗r g (let⊗ Δ₁ Δ₂ cJ cJ' f g')
  let⊗-⊗r2 Δ₁ Δ₂ ax g g' =  ~ ⊗r⊗c2
  let⊗-⊗r2 Δ₁ Δ₂ (uf f) g g' = let⊗-⊗r2 Δ₁ Δ₂ f g g'
  let⊗-⊗r2 {Δ = Δ} Δ₁ Δ₂ {J = J} {J'} (⊗r {Δ = Δ₃} f f₁) g g'
    rewrite cases++-inj₂ (Δ₁ ++ J ∷ []) Δ Δ₂ J' | cases++-inj₂ Δ₁ Δ (Δ₃ ++ Δ₂) J = refl
  let⊗-⊗r2 {Γ = Γ}{Δ} Δ₁ Δ₂ (Il f) g g' = Ic (Δ ++ Δ₁) (Γ ++ Δ₂) (let⊗-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗rIc2)
  let⊗-⊗r2 {Γ = Γ}{Δ} Δ₁ Δ₂ (⊗l f) g g' = ⊗c (Δ ++ Δ₁) (Γ ++ Δ₂) _ _ (let⊗-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c2)
  let⊗-⊗r2 {S} {Δ = Δ₃} Δ₁ Δ₂ (Ic Γ Δ f) g g' = Ic (Δ₃ ++ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (let⊗-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗rIc2 {Γ = Δ₃}{Δ₁ ++ asCxt S Γ})
  let⊗-⊗r2 {S} {Δ = Δ₃} Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g g' = ⊗c (Δ₃ ++ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _ _ (let⊗-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c2 {Γ = Δ₃}{Δ₁ ++ asCxt S Γ})
  
  let⊗-Ic1 : {S T : Stp} {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) → {C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'}
      → (f : S ∣ Γ ⊢ J ⊗ J')(g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ++ Δ₂ ⊢ C)
      → let⊗ Δ₀ (Δ₁ ++ I ∷ Δ₂) cJ cJ' f (Ic (Δ₀ ++ J ∷ J' ∷ Δ₁) Δ₂ g)
        ≗ Ic (Δ₀ ++ asCxt S Γ ++ Δ₁) Δ₂ (let⊗ Δ₀ (Δ₁ ++ Δ₂) cJ cJ' f g)
  let⊗-Ic1 Δ₀ Δ₁ Δ₂ ax g = ⊗cIc
  let⊗-Ic1 Δ₀ Δ₁ Δ₂ (uf f) g = let⊗-Ic1 Δ₀ Δ₁ Δ₂ f g
  let⊗-Ic1 Δ₀ Δ₁ Δ₂ {J = J} {J'} (⊗r {Δ = Δ} f f₁) g
    rewrite cases++-inj₁ (Δ₀ ++ J ∷ []) Δ₁ (I ∷ Δ₂) J' | cases++-inj₁ Δ₀ (Δ ++ Δ₁) (I ∷ Δ₂) J = refl
  let⊗-Ic1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = Ic Δ₀ (Γ ++ Δ₁ ++ I ∷ Δ₂) (let⊗-Ic1 Δ₀ Δ₁ Δ₂ f g) ∙ IcIc {Γ = Δ₀}{Γ ++ Δ₁}
  let⊗-Ic1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₀ (Γ ++ Δ₁ ++ I ∷ Δ₂) _ _ (let⊗-Ic1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗cIc {Γ = Δ₀}{Γ ++ Δ₁}
  let⊗-Ic1 {S} Δ₀ Δ₁ Δ₂ (Ic Γ Δ f) g =  Ic (Δ₀ ++ asCxt S Γ) (Δ ++ Δ₁ ++ I ∷ Δ₂) (let⊗-Ic1 Δ₀ Δ₁ Δ₂ f g) ∙ IcIc {Γ = Δ₀ ++ asCxt S Γ}{Δ ++ Δ₁}
  let⊗-Ic1 {S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₀ ++ asCxt S Γ) (Δ ++ Δ₁ ++ I ∷ Δ₂) _ _ (let⊗-Ic1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗cIc {Γ = Δ₀ ++ asCxt S Γ}{Δ ++ Δ₁}



  let⊗-⊗c1 : {S T : Stp} → {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) → {C J J' K K' : Fma} →
             {cJ : isCl J} {cJ' : isCl J'} {cK : isCl K} {cK' : isCl K'} → 
               (f : S ∣ Γ ⊢ K ⊗ K')(g : T ∣ Δ₀ ++ K ∷ K' ∷ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)  →
              let⊗ Δ₀ (Δ₁ ++ J ⊗ J' ∷ Δ₂) cK cK' f (⊗c (Δ₀ ++ K ∷ K' ∷ Δ₁) Δ₂ cJ cJ' g)
                ≗ ⊗c (Δ₀ ++ asCxt S Γ ++ Δ₁) Δ₂ cJ cJ' (let⊗ Δ₀ (Δ₁ ++ J ∷ J' ∷ Δ₂) cK cK' f g)
  let⊗-⊗c1 Δ₀ Δ₁ Δ₂ ax g = ⊗c⊗c
  let⊗-⊗c1 Δ₀ Δ₁ Δ₂ (uf f) g = let⊗-⊗c1 Δ₀ Δ₁ Δ₂ f g
  let⊗-⊗c1 Δ₀ Δ₁ Δ₂ {J = J} {J'} {K} {K'} (⊗r {Δ = Δ} f f₁) g 
    rewrite cases++-inj₁ (Δ₀ ++ K ∷ []) Δ₁ (J ⊗ J' ∷ Δ₂) K' | cases++-inj₁ Δ₀ (Δ ++ Δ₁) (J ⊗ J' ∷ Δ₂) K = refl
  let⊗-⊗c1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = Ic Δ₀ (Γ ++ Δ₁ ++ _ ∷ Δ₂) (let⊗-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ Ic⊗c {Γ = Δ₀}{Γ ++ Δ₁}
  let⊗-⊗c1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₀ (Γ ++ Δ₁ ++ _ ∷ Δ₂) _ _ (let⊗-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗c⊗c {Γ = Δ₀}{Γ ++ Δ₁}
  let⊗-⊗c1 {S} Δ₀ Δ₁ Δ₂ (Ic Γ Δ f) g =  Ic (Δ₀ ++ asCxt S Γ) (Δ ++ Δ₁ ++ _ ∷ Δ₂) (let⊗-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ Ic⊗c {Γ = Δ₀ ++ asCxt S Γ}{Δ ++ Δ₁}
  let⊗-⊗c1 {S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₀ ++ asCxt S Γ) (Δ ++ Δ₁ ++ _ ∷ Δ₂) _ _ (let⊗-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗c⊗c {Γ = Δ₀ ++ asCxt S Γ}{Δ ++ Δ₁}

  let⊗-Ic2 : {S T : Stp} {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) → {C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'}
      → (f : S ∣ Γ ⊢ J ⊗ J')(g : T ∣ Δ₀ ++ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)
      → let⊗ (Δ₀ ++ I ∷ Δ₁) Δ₂ cJ cJ' f (Ic Δ₀ (Δ₁ ++ J ∷ J' ∷ Δ₂) g)
        ≗ Ic Δ₀ (Δ₁ ++ asCxt S Γ ++ Δ₂) (let⊗ (Δ₀ ++ Δ₁) Δ₂ cJ cJ' f g)
  let⊗-Ic2 Δ₀ Δ₁ Δ₂ ax g = ~ Ic⊗c
  let⊗-Ic2 Δ₀ Δ₁ Δ₂ (uf f) g = let⊗-Ic2 Δ₀ Δ₁ Δ₂ f g
  let⊗-Ic2 Δ₀ Δ₁ Δ₂ {J = J} {J'} (⊗r {Δ = Δ} f f₁) g
    rewrite cases++-inj₂ (I ∷ Δ₁ ++ J ∷ []) Δ₀ Δ₂ J' | cases++-inj₂ (I ∷ Δ₁) Δ₀ (Δ ++ Δ₂) J = refl
  let⊗-Ic2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = Ic (Δ₀ ++ I ∷ Δ₁) (Γ ++ Δ₂) (let⊗-Ic2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ IcIc
  let⊗-Ic2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c (Δ₀ ++ I ∷ Δ₁) (Γ ++ Δ₂) _ _ (let⊗-Ic2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ Ic⊗c
  let⊗-Ic2 {S} Δ₀ Δ₁ Δ₂ (Ic Γ Δ f) g = Ic (Δ₀ ++ I ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (let⊗-Ic2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ IcIc {Γ = Δ₀}{Δ₁ ++ asCxt S Γ}
  let⊗-Ic2 {S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₀ ++ I ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _  _ (let⊗-Ic2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ Ic⊗c {Γ = Δ₀}{Δ₁ ++ asCxt S Γ}
  
  
  let⊗-⊗c2 : {S T : Stp} → {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) →  {C J J' K K' : Fma} →
             {cJ : isCl J} {cJ' : isCl J'} {cK : isCl K} {cK' : isCl K'} → 
               (f : S ∣ Γ ⊢ K ⊗ K')(g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ++ K ∷ K' ∷ Δ₂ ⊢ C)  →
              let⊗ (Δ₀ ++ J ⊗ J' ∷ Δ₁) Δ₂ cK cK' f (⊗c Δ₀ (Δ₁ ++ K ∷ K' ∷ Δ₂) cJ cJ' g)
                ≗ ⊗c Δ₀ (Δ₁ ++ asCxt S Γ ++ Δ₂) cJ cJ' (let⊗ (Δ₀ ++ J ∷ J' ∷ Δ₁) Δ₂ cK cK' f g)
  let⊗-⊗c2 Δ₀ Δ₁ Δ₂ ax g = ~ ⊗c⊗c
  let⊗-⊗c2 Δ₀ Δ₁ Δ₂ (uf f) g = let⊗-⊗c2 Δ₀ Δ₁ Δ₂ f g
  let⊗-⊗c2 Δ₀ Δ₁ Δ₂ {J = J} {J'} {K} {K'} (⊗r {Δ = Δ} f f₁) g
    rewrite cases++-inj₂ (J ⊗ J' ∷ Δ₁ ++ K ∷ []) Δ₀ Δ₂ K' | cases++-inj₂ (J ⊗ J' ∷ Δ₁) Δ₀ (Δ ++ Δ₂) K = refl
  let⊗-⊗c2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = Ic (Δ₀ ++ _ ∷ Δ₁) (Γ ++ Δ₂) (let⊗-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗cIc
  let⊗-⊗c2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c (Δ₀ ++ _ ∷ Δ₁) (Γ ++ Δ₂) _ _ (let⊗-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗c⊗c
  let⊗-⊗c2 {S} Δ₀ Δ₁ Δ₂ (Ic Γ Δ f) g = Ic (Δ₀ ++ _ ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) (let⊗-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗cIc {Γ = Δ₀}{Δ₁ ++ asCxt S Γ}
  let⊗-⊗c2 {S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ cJ cJ' f) g = ⊗c (Δ₀ ++ _ ∷ Δ₁ ++ asCxt S Γ) (Δ ++ Δ₂) _  _ (let⊗-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗c⊗c {Γ = Δ₀}{Δ₁ ++ asCxt S Γ}

-- The rules letI, scut, ccut and let⊗ are compatible with ≗

  mutual
    cong-scut⊗r : ∀{S}{Γ}{Δ}{Δ'}{A}{B}{C}
      → {f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
      → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
      → (p : f ≗ g)(q : f' ≗ g')
      → scut (⊗r f f') h ≗ scut (⊗r g g') h
    cong-scut⊗r ax p q = ⊗r p q
    cong-scut⊗r (⊗r h h') p q = ⊗r (cong-scut⊗r h p q) refl
    cong-scut⊗r {Γ = Γ}{f = f}{g}{f'}{g'} (⊗l h) p q =
      proof≗
      scut f (ccut [] f' h refl)
      ≗〈 cong-scut1 p 〉
      scut g (ccut [] f' h refl)
      ≗〈 cong-scut2 g (cong-ccut1 [] h refl q) 〉
      scut g (ccut [] g' h refl)
      qed≗
    cong-scut⊗r {Γ = Γ₁} {Δ₁} (Ic Γ Δ h) p q =
      Ic (Γ₁ ++ Δ₁ ++ Γ) Δ (cong-scut⊗r h p q)
    cong-scut⊗r {Γ = Γ₁} {Δ₁} (⊗c Γ Δ cJ cJ' h) p q =
      ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ cJ cJ' (cong-scut⊗r h p q)
  
  
  
    cong-scut1 : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
               {f g : S ∣ Γ ⊢ A}  → {h : just A ∣ Δ' ⊢ C} →
               f ≗ g → scut f h ≗ scut g h
    cong-scut1 refl = refl
    cong-scut1 (~ p) = ~ (cong-scut1 p)
    cong-scut1 (p ∙ p₁) = (cong-scut1 p) ∙ (cong-scut1 p₁)
    cong-scut1 (uf p) = uf (cong-scut1 p)
    cong-scut1 (⊗l p) = ⊗l (cong-scut1 p)
    cong-scut1 (Il p) = Il (cong-scut1 p)
    cong-scut1 {h = h} (⊗r p p') = cong-scut⊗r h p p'
    cong-scut1 {h = h} axI = (~ (IlIl-1 h)) ∙ Il (≡-to-≗ (Il-1-scutIr h))
    cong-scut1 {h = h} ax⊗ = 
      proof≗
      h
      ≗〈 ~ ⊗l⊗l-1 h 〉
      ⊗l (⊗l-1 h)
      ≗〈 ⊗l (≡-to-≗ (⊗l-1-scut⊗r h)) 〉
      ⊗l (scut (⊗r ax (uf ax)) h)
      qed≗
    cong-scut1 {h = h} ⊗ruf = scut⊗ruf h
    cong-scut1 {h = h} ⊗rIl = scut⊗rIl h
    cong-scut1 {h = h} ⊗r⊗l = scut⊗r⊗l h
    cong-scut1 {Δ' = Δ'} (Ic Γ Δ p) = Ic Γ (Δ ++ Δ') (cong-scut1 p)
    cong-scut1 ufIc1 = ufIc1
    cong-scut1 IcIc = IcIc
    cong-scut1 ⊗cIc = ⊗cIc
    cong-scut1 ufIc2 = ufIc2
    cong-scut1 IlIc = IlIc
    cong-scut1 ⊗lIc = ⊗lIc
    cong-scut1 {h = ax} (⊗rIc1 {Γ = Γ} {Γ'} {f = f} {g}) = ⊗rIc1
    cong-scut1 {h = ⊗r {_}{Γ₁}{Δ₁} h h₁} (⊗rIc1 {Γ = Γ} {Γ'}  {Δ} {f = f} {g}) =
      ⊗r (cong-scut1 {f = ⊗r (Ic Γ Γ' f) g}{Ic Γ (Γ' ++ Δ) (⊗r f g)}{h} ⊗rIc1) refl
      ∙ ⊗rIc1
    cong-scut1 {h = ⊗l h} (⊗rIc1 {Γ = Γ} {Γ'} {f = f} {g}) = refl
    cong-scut1 {h = Ic Γ₁ Δ h} (⊗rIc1 {Γ = Γ} {Γ'} {Δ₁} {f = f} {g}) =
      Ic (Γ ++ I ∷ Γ' ++ Δ₁ ++ Γ₁) Δ (cong-scut1 {f = ⊗r (Ic Γ Γ' f) g}{Ic Γ (Γ' ++ Δ₁) (⊗r f g)}{h} ⊗rIc1)
      ∙ (~ IcIc {Γ = Γ}{Γ' ++ Δ₁ ++ Γ₁}{Δ})
    cong-scut1 {h = ⊗c Γ₁ Δ cJ cJ' h} (⊗rIc1 {Γ = Γ} {Γ'} {Δ₁} {f = f} {g}) =
      ⊗c (Γ ++ I ∷ Γ' ++ Δ₁ ++ Γ₁) Δ cJ cJ' (cong-scut1 {f = ⊗r (Ic Γ Γ' f) g}{Ic Γ (Γ' ++ Δ₁) (⊗r f g)}{h} ⊗rIc1)
      ∙ (~ Ic⊗c {Γ = Γ}{Γ' ++ Δ₁ ++ Γ₁}{Δ}) 
    cong-scut1 {Δ' = .[]} {h = ax} (⊗rIc2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) = ⊗rIc2
    cong-scut1 {Δ' = ._} {h = ⊗r {_}{Γ₁}{Δ₁} h h₁} (⊗rIc2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) =
      ⊗r (cong-scut1 {f = ⊗r f (Ic Δ Δ'' g)}{Ic (Γ ++ Δ) Δ'' (⊗r f g)}{h} ⊗rIc2) refl
      ∙ ⊗rIc1 {Γ = Γ ++ Δ} {Δ'' ++ Γ₁} {Δ₁}
    cong-scut1 {Δ' = Δ'} {h = ⊗l h} (⊗rIc2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) =
      cong-scut2 f (ccut-Ic [] Δ Δ'' g h refl) ∙ scut-Ic Δ (Δ'' ++ Δ') f (ccut [] g h refl)
    cong-scut1 {Δ' = .(Γ₁ ++ I ∷ Δ₁)} {h = Ic Γ₁ Δ₁ h} (⊗rIc2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) =
      Ic (Γ ++ Δ ++ I ∷ Δ'' ++ Γ₁) Δ₁ (cong-scut1 {f = ⊗r f (Ic Δ Δ'' g)}{Ic (Γ ++ Δ) Δ'' (⊗r f g)}{h} ⊗rIc2)
      ∙ (~ IcIc {Γ = Γ ++ Δ}{Δ'' ++ Γ₁}{Δ₁})
    cong-scut1 {Δ' = .(Γ₁ ++ _ ⊗ _ ∷ Δ₁)} {h = ⊗c Γ₁ Δ₁ cJ cJ' h} (⊗rIc2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) =
      ⊗c (Γ ++ Δ ++ I ∷ Δ'' ++ Γ₁) Δ₁ cJ cJ' (cong-scut1 {f = ⊗r f (Ic Δ Δ'' g)}{Ic (Γ ++ Δ) Δ'' (⊗r f g)}{h} ⊗rIc2)
      ∙ (~ Ic⊗c {Γ = Γ ++ Δ}{Δ'' ++ Γ₁}{Δ₁})
    cong-scut1 {Δ' = Δ'} (⊗c Γ Δ cJ cJ' p) = ⊗c Γ (Δ ++ Δ') cJ cJ' (cong-scut1 p)
    cong-scut1 uf⊗c1 = uf⊗c1
    cong-scut1 ⊗c⊗c = ⊗c⊗c
    cong-scut1 Ic⊗c = Ic⊗c
    cong-scut1 uf⊗c2 = uf⊗c2
    cong-scut1 Il⊗c = Il⊗c
    cong-scut1 ⊗l⊗c = ⊗l⊗c
    cong-scut1 {h = ax} (⊗r⊗c1 {Γ = Γ} {Γ'} {f = f} {g}) = ⊗r⊗c1
    cong-scut1 {h = ⊗r {_}{Γ₁}{Δ₁} h h₁} (⊗r⊗c1 {Γ = Γ} {Γ'}  {Δ} {f = f} {g}) =
      ⊗r (cong-scut1 {f = ⊗r (⊗c Γ Γ' _ _ f) g}{⊗c Γ (Γ' ++ Δ) _ _ (⊗r f g)}{h} ⊗r⊗c1) refl
      ∙ ⊗r⊗c1
    cong-scut1 {h = ⊗l h} (⊗r⊗c1 {Γ = Γ} {Γ'} {f = f} {g}) = refl
    cong-scut1 {h = Ic Γ₁ Δ h} (⊗r⊗c1 {Γ = Γ} {Γ'} {Δ₁} {f = f} {g}) =
      Ic (Γ ++ _ ∷ Γ' ++ Δ₁ ++ Γ₁) Δ (cong-scut1 {f = ⊗r (⊗c Γ Γ' _ _ f) g}{⊗c Γ (Γ' ++ Δ₁) _ _ (⊗r f g)}{h} ⊗r⊗c1)
      ∙ (~ ⊗cIc {Γ = Γ}{Γ' ++ Δ₁ ++ Γ₁}{Δ})
    cong-scut1 {h = ⊗c Γ₁ Δ cJ cJ' h} (⊗r⊗c1 {Γ = Γ} {Γ'} {Δ₁} {f = f} {g}) =
      ⊗c (Γ ++ _ ∷ Γ' ++ Δ₁ ++ Γ₁) Δ cJ cJ' (cong-scut1 {f = ⊗r (⊗c Γ Γ' _ _ f) g}{⊗c Γ (Γ' ++ Δ₁) _ _ (⊗r f g)}{h} ⊗r⊗c1)
      ∙ (~ ⊗c⊗c {Γ = Γ}{Γ' ++ Δ₁ ++ Γ₁}{Δ}) 
    cong-scut1 {Δ' = .[]} {h = ax} (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) = ⊗r⊗c2
    cong-scut1 {Δ' = ._} {h = ⊗r {_}{Γ₁}{Δ₁} h h₁} (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) =
      ⊗r (cong-scut1 {f = ⊗r f (⊗c Δ Δ'' _ _ g)}{⊗c (Γ ++ Δ) Δ'' _ _ (⊗r f g)}{h} ⊗r⊗c2) refl
      ∙ ⊗r⊗c1 {Γ = Γ ++ Δ} {Δ'' ++ Γ₁} {Δ₁}
    cong-scut1 {Δ' = Δ'} {h = ⊗l h} (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) = 
      cong-scut2 f (ccut-⊗c [] Δ Δ'' g h refl) ∙ scut-⊗c Δ (Δ'' ++ Δ') f (ccut [] g h refl)
    cong-scut1 {Δ' = .(Γ₁ ++ I ∷ Δ₁)} {h = Ic Γ₁ Δ₁ h} (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) =
      Ic (Γ ++ Δ ++ _ ∷ Δ'' ++ Γ₁) Δ₁ (cong-scut1 {f = ⊗r f (⊗c Δ Δ'' _ _ g)}{⊗c (Γ ++ Δ) Δ'' _ _ (⊗r f g)}{h} ⊗r⊗c2)
      ∙ (~ ⊗cIc {Γ = Γ ++ Δ}{Δ'' ++ Γ₁}{Δ₁})
    cong-scut1 {Δ' = .(Γ₁ ++ _ ⊗ _ ∷ Δ₁)} {h = ⊗c Γ₁ Δ₁ cJ cJ' h} (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) =
      ⊗c (Γ ++ Δ ++ _ ∷ Δ'' ++ Γ₁) Δ₁ cJ cJ' (cong-scut1 {f = ⊗r f (⊗c Δ Δ'' _ _ g)}{⊗c (Γ ++ Δ) Δ'' _ _ (⊗r f g)}{h} ⊗r⊗c2)
      ∙ (~ ⊗c⊗c {Γ = Γ ++ Δ}{Δ'' ++ Γ₁}{Δ₁})

    cong-scut2 : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
            (h : S ∣ Γ ⊢ A)  → {f g : just A ∣ Δ' ⊢ C} →
            f ≗ g → scut h f ≗ scut h g
    cong-scut2 ax p = p
    cong-scut2 (uf h) p = uf (cong-scut2 h p)
    cong-scut2 Ir {f}{g} p =
      proof≗
      scut Ir f
      ≗〈 ≡-to-≗ (sym (Il-1-scutIr f)) 〉
      Il-1 f
      ≗〈 congIl-1 p 〉
      Il-1 g
      ≗〈 ≡-to-≗ (Il-1-scutIr g) 〉
      scut Ir g
      qed≗
    cong-scut2 (⊗r h h') refl = refl
    cong-scut2 (⊗r h h') (~ p) = ~ (cong-scut2 (⊗r h h') p)
    cong-scut2 (⊗r h h') (p ∙ p') = (cong-scut2 (⊗r h h') p) ∙ (cong-scut2 (⊗r h h') p')
    cong-scut2 (⊗r {Γ = Γ} h h') (⊗l p) = cong-scut2 h (cong-ccut2 [] refl p)
    cong-scut2 (⊗r h h') (⊗r p p') = ⊗r (cong-scut2 (⊗r h h') p) p'
    cong-scut2 (⊗r h h') ax⊗ =
      ⊗r (~ (≡-to-≗ (scut-unit h))) (~ (≡-to-≗ (scut-unit h'))) ∙ ~ scut⊗r h ax (scut h' ax)
    cong-scut2 (⊗r {Γ = Γ} h h') (⊗r⊗l {f = f}{g}) = ~ (scut⊗r h (ccut [] h' f refl) g)
    cong-scut2 (⊗r {Γ = Γ₁} {Δ₁} h h') (Ic Γ Δ p) = Ic (Γ₁ ++ Δ₁ ++ Γ) Δ (cong-scut2 (⊗r h h') p)
    cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (IcIc {Γ = Γ₁} {Δ₁} {Λ}) = IcIc {Γ = Γ ++ Δ ++ Γ₁} {Δ₁} {Λ}
    cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (⊗cIc {Γ = Γ₁} {Δ₁} {Λ}) = ⊗cIc {Γ = Γ ++ Δ ++ Γ₁} {Δ₁} {Λ}
    cong-scut2 (⊗r {Δ = Δ} h h') (⊗lIc {Γ} {Δ₁} {f = f}) = scut-Ic (Δ ++ Γ) Δ₁ h (ccut [] h' f refl)
    cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (⊗rIc1 {Γ = Γ₁} {Γ'} {Δ₁}) = ⊗rIc1 {Γ = Γ ++ Δ ++ Γ₁} {Γ'} {Δ₁}
    cong-scut2 (⊗r h h') ⊗rIc2 = ⊗rIc2
    cong-scut2 (⊗r {Γ = Γ₁} {Δ₁} h h') (⊗c Γ Δ _ _ p) = ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ _ _ (cong-scut2 (⊗r h h') p)
    cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (Ic⊗c {Γ = Γ₁} {Δ₁} {Λ}) = Ic⊗c {Γ = Γ ++ Δ ++ Γ₁} {Δ₁} {Λ}
    cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (⊗c⊗c {Γ = Γ₁} {Δ₁} {Λ}) = ⊗c⊗c {Γ = Γ ++ Δ ++ Γ₁} {Δ₁} {Λ}
    cong-scut2 (⊗r {Δ = Δ} h h') (⊗l⊗c {Γ} {Δ₁} {f = f}) = scut-⊗c (Δ ++ Γ) Δ₁ h (ccut [] h' f refl)
    cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (⊗r⊗c1 {Γ = Γ₁} {Γ'} {Δ₁}) = ⊗r⊗c1 {Γ = Γ ++ Δ ++ Γ₁} {Γ'} {Δ₁}
    cong-scut2 (⊗r h h') ⊗r⊗c2 = ⊗r⊗c2
    cong-scut2 (Il h) p = Il (cong-scut2 h p)
    cong-scut2 (⊗l h) p = ⊗l (cong-scut2 h p)
    cong-scut2 {Δ' = Δ'} (Ic Γ Δ h) p = Ic Γ (Δ ++ Δ') (cong-scut2 h p)
    cong-scut2 {Δ' = Δ'} (⊗c Γ Δ cJ cJ' h) p = ⊗c Γ (Δ ++ Δ') cJ cJ' (cong-scut2 h p)
  
    cong-ccut1 : {S T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
               {f f' : S ∣ Γ ⊢ A}(g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
               f ≗ f' → ccut Δ₀ f g r ≗ ccut Δ₀ f' g r
    cong-ccut1 Δ₀ ax r p = ⊥-elim ([]disj∷ Δ₀ r)
    cong-ccut1 Δ₀ (uf g) r p with cases∷ Δ₀ r
    cong-ccut1 {nothing} .[] (uf g) r p | inj₁ (refl , refl , refl) = cong-scut1 p
    cong-ccut1 {just x} .[] (uf g) r p | inj₁ (refl , refl , refl) = uf (cong-scut1 p) 
    cong-ccut1 .(_ ∷ Δ₀) (uf g) r p | inj₂ (Δ₀ , refl , refl) = uf (cong-ccut1 Δ₀ g refl p)
    cong-ccut1 Δ₀ Ir r p = ⊥-elim ([]disj∷ Δ₀ r)
    cong-ccut1 Δ₀ {Δ'} (⊗r {Γ = Γ}{Δ} g g') r p with cases++ Δ₀ Γ Δ' Δ r
    cong-ccut1 Δ₀ (⊗r g g') r p | inj₁ (Γ₀ , refl , refl) = ⊗r (cong-ccut1 Δ₀ g refl p) refl
    cong-ccut1 ._ (⊗r g g') r p | inj₂ (Γ₀ , refl , refl) = ⊗r refl (cong-ccut1 Γ₀ g' refl p)
    cong-ccut1 Δ₀ (Il g) refl p = Il (cong-ccut1 Δ₀ g refl p)
    cong-ccut1 Δ₀ (⊗l {B = B} g) refl p = ⊗l (cong-ccut1 (B ∷ Δ₀) g refl p)
    cong-ccut1 Δ₀ {Δ'} (Ic Γ Δ g) r p with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    cong-ccut1 {S}{Γ = Γ} Δ₀ {.(Γ₀ ++ I ∷ Δ)} (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl p | inj₁ (Γ₀ , refl , refl) =
      Ic (Δ₀ ++ asCxt S Γ ++ Γ₀) Δ (cong-ccut1 Δ₀ g refl p)
    cong-ccut1 .Γ {.Δ} (Ic Γ Δ g) refl p | inj₂ ([] , refl , refl) = cong-letI1 Γ Δ g p
    cong-ccut1 {S}{Γ = Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} (Ic Γ .(Γ₀ ++ _ ∷ Δ') g) refl p | inj₂ (.I ∷ Γ₀ , refl , refl) =
      Ic Γ (Γ₀ ++ asCxt S Γ₁ ++ Δ') (cong-ccut1 (Γ ++ Γ₀) g refl p)
    cong-ccut1 Δ₀ {Δ'} (⊗c Γ Δ cJ cJ' g) r p with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    cong-ccut1 {S}{Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ _ _ g) refl p | inj₁ (Γ₀ , refl , refl) =
      ⊗c (Δ₀ ++ asCxt S Γ ++ Γ₀) Δ _ _ (cong-ccut1 Δ₀ g refl p)
    cong-ccut1 .Γ {.Δ} (⊗c Γ Δ _ _ g) refl p | inj₂ ([] , refl , refl) = cong-let⊗1 Γ Δ g p
    cong-ccut1 {S}{Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} (⊗c Γ .(Γ₀ ++ _ ∷ Δ') _ _ g) refl p | inj₂ (_ ∷ Γ₀ , refl , refl) = 
      ⊗c Γ (Γ₀ ++ asCxt S Γ₁ ++ Δ') _ _ (cong-ccut1 (Γ ++ _ ∷ _ ∷  Γ₀) g refl p)
  
    cong-let⊗1 : {S T : Stp} {Γ : Cxt} → (Δ₀ Δ' : Cxt) → {C J J' : Fma} {cJ : isCl J}{cJ' : isCl J'} → 
                 {f f' : S ∣ Γ ⊢ J ⊗ J'}(g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ' ⊢ C)  → 
                 f ≗ f' → let⊗ Δ₀ Δ' cJ cJ' f g ≗ let⊗ Δ₀ Δ' cJ cJ' f' g
    cong-let⊗1 Δ₀ Δ' g refl = refl
    cong-let⊗1 Δ₀ Δ' g (~ p) = ~ cong-let⊗1 Δ₀ Δ' g p
    cong-let⊗1 Δ₀ Δ' g (p ∙ p₁) = cong-let⊗1 Δ₀ Δ' g p ∙ cong-let⊗1 Δ₀ Δ' g p₁
    cong-let⊗1 Δ₀ Δ' g (uf p) = cong-let⊗1 Δ₀ Δ' g p
    cong-let⊗1 {Γ = Γ} Δ₀ Δ' g (⊗l {g = g'} p) = ⊗c Δ₀ (Γ ++ Δ') _ _ (cong-let⊗1 Δ₀ Δ' g p) ∙
      ≡-to-≗ (cong₂ (λ x y → ⊗c Δ₀ (Γ ++ Δ') x y (let⊗ Δ₀ Δ' _ _ g' g)) (uniq-cl _ _) (uniq-cl _ _))
    cong-let⊗1 {Γ = Γ} Δ₀ Δ' g (Il p) = Ic Δ₀ (Γ ++ Δ') (cong-let⊗1 Δ₀ Δ' g p)
    cong-let⊗1 Δ₀ Δ' g ax⊗ =
      ≡-to-≗ (cong₂ (λ x y → ⊗c Δ₀ Δ' x y g) (uniq-cl _ _) (uniq-cl _ _))
      ∙ ⊗c Δ₀ Δ' _ _
          (≡-to-≗ (sym (trans (ccut-ax Δ₀ (ccut (Δ₀ ++ _ ∷ []) (uf ax) g refl) refl)
                              (ccut-unit (Δ₀ ++ _ ∷ []) g refl))) ) 
    cong-let⊗1 Δ₀ Δ' g (⊗r {g = g₁} {f'} p q) =
      cong-ccut1 Δ₀ (ccut (Δ₀ ++ _ ∷ []) f' g refl) refl p
      ∙  cong-ccut2 Δ₀ {f = g₁} refl (cong-ccut1 (Δ₀ ++ _ ∷ []) g refl q) 
    cong-let⊗1 Δ₀ Δ' g (⊗ruf {f = f} {g₁}) = ≡-to-≗ (ccut-uf Δ₀ f (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl)
    cong-let⊗1 Δ₀ Δ' g (⊗rIl {Γ} {f = f} {g₁}) =
      ≡-to-≗ (sym (ccut-uf Δ₀ (Il f) (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl))
      ∙ cong-ccut1 Δ₀ (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl ufIc1
      ∙ ccut-Ic Δ₀ [] Γ f (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl
    cong-let⊗1 Δ₀ Δ' g (⊗r⊗l {Γ}{Δ} {f = f}{g₁}) = 
      ≡-to-≗ (sym (ccut-uf Δ₀ (⊗l f) (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl))
      ∙ cong-ccut1 Δ₀ (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl uf⊗c1
      ∙ ccut-⊗c Δ₀ [] Γ (uf f) (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl
      ∙ ⊗c Δ₀ (Γ ++ Δ ++ Δ') _ _ (≡-to-≗ (ccut-uf Δ₀ f (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl))
    cong-let⊗1 Δ₀ Δ' g (⊗rIc1 {Γ = Γ} {Γ'} {f = f} {g₁}) = ccut-Ic Δ₀ Γ Γ' f (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl
    cong-let⊗1 Δ₀ Δ' {J = J} g (⊗rIc2 {Γ = Γ} {Δ} {Δ''} {f = f} {g₁}) with cong-ccut2 Δ₀ {f = f} refl (ccut-Ic (Δ₀ ++ _ ∷ []) Δ Δ'' g₁ g refl)
    ... | ih rewrite cases++-inj₁ Δ₀ Δ (I ∷ Δ'' ++ Δ') J = ih
    cong-let⊗1 Δ₀ Δ' g (⊗r⊗c1 {Γ = Γ} {Γ'} {f = f} {g₁}) = ccut-⊗c Δ₀ Γ Γ' f (ccut (Δ₀ ++ _ ∷ []) g₁ g refl) refl
    cong-let⊗1 Δ₀ Δ' {J = K} g (⊗r⊗c2 {Δ = Δ} {Δ''} {J = J}{J'}{cJ = cJ}{cJ'} {f = f} {g₁}) with cong-ccut2 Δ₀ {f = f} refl (ccut-⊗c (Δ₀ ++ _ ∷ []) Δ Δ'' {cJ = cJ}{cJ'} g₁ g refl)
    ... | ih rewrite cases++-inj₁ Δ₀ Δ (J ⊗ J' ∷ Δ'' ++ Δ') K = ih 
    cong-let⊗1 {S} Δ₀ Δ' g (Ic Γ Δ p) = Ic (Δ₀ ++ asCxt S Γ) (Δ ++ Δ') (cong-let⊗1 {S} Δ₀ Δ' g p)
    cong-let⊗1 Δ₀ Δ' g ufIc1 = refl
    cong-let⊗1 {S} Δ₀ Δ' g (IcIc {Γ = Γ} {Δ} {Λ}) = IcIc {Γ = Δ₀ ++ asCxt S Γ}{Δ}{Λ ++ Δ'}
    cong-let⊗1 {S} Δ₀ Δ' g (⊗cIc {Γ = Γ} {Δ} {Λ}) = ⊗cIc {Γ = Δ₀ ++ asCxt S Γ}{Δ}{Λ ++ Δ'}
    cong-let⊗1 Δ₀ Δ' g ufIc2 = refl
    cong-let⊗1 Δ₀ Δ' g IlIc = IcIc
    cong-let⊗1 Δ₀ Δ' g (⊗lIc {Γ} {Δ} {A} {B} {f = f}) = ⊗cIc {Γ = Δ₀}{Γ}{Δ ++ Δ'} ∙
      Ic (Δ₀ ++ A ⊗ B ∷ Γ) (Δ ++ Δ') (≡-to-≗ (cong₂ (λ x y → ⊗c Δ₀ (Γ ++ Δ ++ Δ') x y (let⊗ Δ₀ Δ' _ _ f g)) (uniq-cl _ _) (uniq-cl _ _))) 
    cong-let⊗1 {S} Δ₀ Δ' g (⊗c Γ Δ _ _ p) = ⊗c (Δ₀ ++ asCxt S Γ) (Δ ++ Δ') _ _ (cong-let⊗1 {S} Δ₀ Δ' g p)
    cong-let⊗1 Δ₀ Δ' g (uf⊗c1 {Γ} {f = f}) = ≡-to-≗ (cong₂ (λ x y → ⊗c Δ₀ (Γ ++ Δ') x y (let⊗ Δ₀ Δ' _ _ f g)) (uniq-cl _ _) (uniq-cl _ _))
    cong-let⊗1 {S} Δ₀ Δ' g (Ic⊗c {Γ = Γ} {Δ} {Λ}) = Ic⊗c {Γ = Δ₀ ++ asCxt S Γ}{Δ}{Λ ++ Δ'}
    cong-let⊗1 {S} Δ₀ Δ' g (⊗c⊗c {Γ = Γ} {Δ} {Λ}) = ⊗c⊗c {Γ = Δ₀ ++ asCxt S Γ}{Δ}{Λ ++ Δ'}
    cong-let⊗1 Δ₀ Δ' g uf⊗c2 = refl
    cong-let⊗1 Δ₀ Δ' g Il⊗c = Ic⊗c
    cong-let⊗1 Δ₀ Δ' g (⊗l⊗c {Γ} {Δ} {A} {B} {f = f}) = ⊗c⊗c {Γ = Δ₀}{Γ}{Δ ++ Δ'} ∙
      ⊗c (Δ₀ ++ A ⊗ B ∷ Γ) (Δ ++ Δ') _ _ (≡-to-≗ (cong₂ (λ x y → ⊗c Δ₀ (Γ ++ _ ∷ _ ∷ Δ ++ Δ') x y (let⊗ Δ₀ Δ' _ _ f g)) (uniq-cl _ _) (uniq-cl _ _)))
  
    cong-let⊗2 : {S T : Stp} {Γ : Cxt} → (Δ₀ Δ' : Cxt) → {C J J' : Fma} {cJ : isCl J}{cJ' : isCl J'} → 
                 (f : S ∣ Γ ⊢ J ⊗ J'){g g' : T ∣ Δ₀ ++ J ∷ J' ∷ Δ' ⊢ C}  → 
                 g ≗ g' → let⊗ Δ₀ Δ' cJ cJ' f g ≗ let⊗ Δ₀ Δ' cJ cJ' f g'
    cong-let⊗2 Δ₀ Δ' ax p = ⊗c Δ₀ Δ' _ _ p
    cong-let⊗2 Δ₀ Δ' (uf f) p = cong-let⊗2 Δ₀ Δ' f p
    cong-let⊗2 Δ₀ Δ' (⊗r f f') p = cong-ccut2 Δ₀ {f = f} refl (cong-ccut2 (Δ₀ ++ _ ∷ []) {f = f'} refl p) 
    cong-let⊗2 Δ₀ Δ' (Il {Γ = Γ} f) p = Ic Δ₀ (Γ ++ Δ') (cong-let⊗2 Δ₀ Δ' f p)
    cong-let⊗2 Δ₀ Δ' (⊗l {Γ = Γ} f) p = ⊗c Δ₀ (Γ ++ Δ') _ _ (cong-let⊗2 Δ₀ Δ' f p)
    cong-let⊗2 {S} Δ₀ Δ' (Ic Γ Δ f) p = Ic (Δ₀ ++ asCxt S Γ) (Δ ++ Δ') (cong-let⊗2 Δ₀ Δ' f p)
    cong-let⊗2 {S} Δ₀ Δ' (⊗c Γ Δ cJ cJ' f) p = ⊗c (Δ₀ ++ asCxt S Γ) (Δ ++ Δ') cJ cJ' (cong-let⊗2 Δ₀ Δ' f p)
  
    
    cong-ccut2 : {S T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
               {f : S ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C}  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
               g ≗ g' → ccut Δ₀ f g r ≗ ccut Δ₀ f g' r
    cong-ccut2 Δ₀ r refl = refl
    cong-ccut2 Δ₀ r (~ p) = ~ cong-ccut2 Δ₀ r p
    cong-ccut2 Δ₀ r (p ∙ p₁) = (cong-ccut2 Δ₀ r p) ∙ (cong-ccut2 Δ₀ r p₁)
    cong-ccut2 Δ₀ r (uf p) with cases∷ Δ₀ r
    cong-ccut2 {nothing} .[] {f = f} r (uf p) | inj₁ (refl , refl , refl) = cong-scut2 f p 
    cong-ccut2 {just x} .[] {f = f} r (uf p) | inj₁ (refl , refl , refl) = uf (cong-scut2 f p) 
    cong-ccut2 .(_ ∷ Γ₀) r (uf p) | inj₂ (Γ₀ , refl , refl) = uf (cong-ccut2 Γ₀ refl p)
    cong-ccut2 Δ₀ refl (⊗l {B = B} p) = ⊗l (cong-ccut2 (B ∷ Δ₀) refl p)
    cong-ccut2 Δ₀ refl (Il p) = Il (cong-ccut2 Δ₀ refl p)
    cong-ccut2 Δ₀ {Δ'} r (⊗r {Γ = Γ}{Δ} p p') with cases++ Δ₀ Γ Δ' Δ r
    cong-ccut2 Δ₀ r (⊗r p p') | inj₁ (Γ₀ , refl , refl) = ⊗r (cong-ccut2 Δ₀ refl p) p'
    cong-ccut2 ._ r (⊗r p p') | inj₂ (Γ₀ , refl , refl) = ⊗r p (cong-ccut2 Γ₀ refl p')
    cong-ccut2 Δ₀ r axI = ⊥-elim ([]disj∷ Δ₀ r)
    cong-ccut2 Δ₀ r ax⊗ = ⊥-elim ([]disj∷ Δ₀ r)
    cong-ccut2 Δ₀ {Δ'} r (⊗ruf {Γ} {Δ}) with cases++ Δ₀ (_ ∷ Γ) Δ' Δ r
    cong-ccut2 {nothing} [] {.(Γ₀ ++ Δ)} {f = f} refl (⊗ruf {.Γ₀} {Δ} {f = f₁} {g}) | inj₁ (Γ₀ , refl , refl) = ~ scut⊗r f f₁ g
    cong-ccut2 {just x} [] {.(Γ₀ ++ Δ)} {f = f} refl (⊗ruf {.Γ₀} {Δ} {f = f₁} {g}) | inj₁ (Γ₀ , refl , refl) = ⊗ruf ∙ uf (~ scut⊗r f f₁ g)
    cong-ccut2 (x ∷ Δ₀) {.(Γ₀ ++ Δ)} {A} {f = f} refl (⊗ruf {.(Δ₀ ++ A ∷ Γ₀)} {Δ} {f = f₁} {g}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ Δ A = ⊗ruf
    cong-ccut2 .(_ ∷ Γ ++ Γ₀) {Δ'} {A} refl (⊗ruf {Γ} {.(Γ₀ ++ A ∷ Δ')}) | inj₂ (Γ₀ , refl , refl)
      rewrite cases++-inj₂ Γ₀ Γ Δ' A = ⊗ruf
    cong-ccut2 Δ₀ {Δ'} r (⊗rIl {Γ} {Δ}) with cases++ Δ₀ Γ Δ' Δ r
    cong-ccut2 Δ₀ {.(Γ₀ ++ Δ)} refl (⊗rIl {.(Δ₀ ++ _ ∷ Γ₀)} {Δ}) | inj₁ (Γ₀ , refl , refl) = ⊗rIl
    cong-ccut2 .(Γ ++ Γ₀) {Δ'} refl (⊗rIl {Γ} {.(Γ₀ ++ _ ∷ Δ')}) | inj₂ (Γ₀ , refl , refl) = ⊗rIl
    cong-ccut2 Δ₀ {Δ'} r (⊗r⊗l {Γ} {Δ}) with cases++ Δ₀ Γ Δ' Δ r
    cong-ccut2 Δ₀ {.(Γ₀ ++ Δ)} {A} refl (⊗r⊗l {.(Δ₀ ++ A ∷ Γ₀)} {Δ}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ Δ A = ⊗r⊗l
    cong-ccut2 .(Γ ++ Γ₀) {Δ'} {A} refl (⊗r⊗l {Γ} {.(Γ₀ ++ A ∷ Δ')}) | inj₂ (Γ₀ , refl , refl) 
      rewrite cases++-inj₂ Γ₀ Γ Δ' A = ⊗r⊗l
    cong-ccut2 Δ₀ {Δ'} r (Ic Γ Δ p) with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    cong-ccut2 {S}{Γ = Γ} Δ₀ {.(Γ₀ ++ I ∷ Δ)} refl (Ic .(Δ₀ ++ _ ∷ Γ₀) Δ p) | inj₁ (Γ₀ , refl , refl) = Ic (Δ₀ ++ asCxt S Γ ++ Γ₀) Δ ( cong-ccut2 Δ₀ refl p )
    cong-ccut2 .Γ {.Δ} {f = f} refl (Ic Γ Δ p) | inj₂ ([] , refl , refl) = cong-letI2 Γ Δ f p
    cong-ccut2 {S} {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} refl (Ic Γ .(Γ₀ ++ _ ∷ Δ') p) | inj₂ (.I ∷ Γ₀ , refl , refl) = Ic Γ (Γ₀ ++ asCxt S Γ₁ ++ Δ') (cong-ccut2 (Γ ++ Γ₀) refl p)
    cong-ccut2 {nothing} [] {Δ'} {f = f} refl (ufIc1 {f = f₁}) = ~ letI-[] Δ' f f₁
    cong-ccut2 {just x} [] {Δ'} {f = f} refl (ufIc1 {f = f₁}) = ~ letI-[]-j Δ' f f₁
    cong-ccut2 (.I ∷ Δ₀) refl ufIc1 = ufIc1
    cong-ccut2 Δ₀ {Δ'} r (IcIc {Γ = Γ} {Δ} {Λ}) with cases++ Δ₀ (Γ ++ I ∷ Δ) Δ' (I ∷ Λ) r
    cong-ccut2 Δ₀ {.(Γ₀ ++ I ∷ Λ)} r (IcIc {Γ = Γ} {Δ} {Λ}) | inj₁ (Γ₀ , p , refl) with cases++ Δ₀ Γ Γ₀ (I ∷ Δ) p
    cong-ccut2 {S}{Γ = Γ} Δ₀ {.((Γ₀' ++ I ∷ Δ) ++ I ∷ Λ)} {A} refl (IcIc {Γ = .(Δ₀ ++ A ∷ Γ₀')} {Δ} {Λ}) | inj₁ (.(Γ₀' ++ I ∷ Δ) , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (I ∷ Δ ++ I ∷ Λ)  A | cases++-inj₁ Δ₀ Γ₀' (I ∷ Δ ++ Λ) A | cases++-inj₁ Δ₀ (Γ₀' ++ Δ) (I ∷ Λ) A = IcIc {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀'}{Δ}{Λ}
    cong-ccut2 Δ₀ {.(Γ₀ ++ I ∷ Λ)}  {f = f'} refl (IcIc {Γ = .Δ₀} {.Γ₀} {Λ} {f = f}) | inj₁ (Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Δ₀ (Γ₀ ++ I ∷ Λ) I | cases++-inj₂ [] Δ₀ (Γ₀ ++ Λ) I = letI-Ic1 Δ₀ Γ₀ Λ f' f
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ I ∷ Γ₀') {.(Γ₀ ++ I ∷ Λ)} {A} refl (IcIc {Γ = Γ} {.(Γ₀' ++ A ∷ Γ₀)} {Λ}) | inj₁ (Γ₀ , refl , refl) | inj₂ (.I ∷ Γ₀' , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀') Γ (Γ₀ ++ I ∷ Λ) A | cases++-inj₁ (Γ ++ Γ₀') Γ₀ (I ∷ Λ) A | cases++-inj₂ (I ∷ Γ₀') Γ (Γ₀ ++ Λ) A = IcIc {Γ = Γ}{Γ₀' ++ asCxt S Γ₁ ++ Γ₀}{Λ}
    cong-ccut2 .(Γ ++ I ∷ Δ) {.Λ} {f = f} refl (IcIc {Γ = Γ} {Δ} {Λ} {f = g}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ (I ∷ Δ) Γ Λ I | cases++-inj₂ [] (Γ ++ Δ) Λ I  = ~ letI-Ic2 Γ Δ Λ f g
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ I ∷ Δ ++ I ∷ Γ₀) {Δ'} {A} refl (IcIc {Γ = Γ} {Δ} {.(Γ₀ ++ A ∷ Δ')}) | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Δ ++ I ∷ Γ₀) Γ Δ' A | cases++-inj₂ (I ∷ Δ ++ Γ₀) Γ Δ' A | cases++-inj₂ (I ∷ Γ₀) (Γ ++ Δ) Δ' A = IcIc {Γ = Γ}{Δ}{Γ₀ ++ asCxt S Γ₁ ++ Δ'}
    cong-ccut2 Δ₀ {Δ'} r (⊗cIc {Γ = Γ} {Δ} {Λ}) with cases++ Δ₀ (Γ ++ _ ∷ Δ) Δ' (I ∷ Λ) r
    cong-ccut2 Δ₀ {.(Γ₀ ++ I ∷ Λ)} r (⊗cIc {Γ = Γ} {Δ} {Λ} {J = J}{J'}) | inj₁ (Γ₀ , p , refl) with cases++ Δ₀ Γ Γ₀ (_ ∷ Δ) p
    cong-ccut2 {S}{Γ = Γ} Δ₀ {.((Γ₀' ++ _ ∷ Δ) ++ _ ∷ Λ)} {A} refl (⊗cIc {Γ = .(Δ₀ ++ A ∷ Γ₀')} {Δ} {Λ} {J = J}{J'}) | inj₁ (.(Γ₀' ++ _ ∷ Δ) , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Δ ++ I ∷ Λ)  A | cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Δ ++ Λ) A | cases++-inj₁ Δ₀ (Γ₀' ++ J ∷ J' ∷ Δ) (I ∷ Λ) A = ⊗cIc {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀'}{Δ}{Λ}
    cong-ccut2 Δ₀ {.(Γ₀ ++ _ ∷ Λ)}  {f = f'} refl (⊗cIc {Γ = .Δ₀} {.Γ₀} {Λ} {J = J}{J'} {f = f}) | inj₁ (Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Δ₀ (Γ₀ ++ I ∷ Λ) (J ⊗ J') | cases++-inj₂ [] Δ₀ (Γ₀ ++ Λ) (J ⊗ J') = let⊗-Ic1 Δ₀ Γ₀ Λ f' f
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ _ ∷ Γ₀') {.(Γ₀ ++ _ ∷ Λ)} {A} refl (⊗cIc {Γ = Γ} {.(Γ₀' ++ A ∷ Γ₀)} {Λ} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (_ ∷ Γ₀' , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Γ₀ ++ I ∷ Λ) A | cases++-inj₁ (Γ ++ J ∷ J' ∷ Γ₀') Γ₀ (I ∷ Λ) A | cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Γ₀ ++ Λ) A = ⊗cIc {Γ = Γ}{Γ₀' ++ asCxt S Γ₁ ++ Γ₀}{Λ} 
    cong-ccut2 .(Γ ++ _ ∷ Δ) {.Λ} {f = f} refl (⊗cIc {Γ = Γ} {Δ} {Λ} {J = J}{J'} {f = g}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Δ) Γ Λ I | cases++-inj₂ [] (Γ ++ J ∷ J' ∷ Δ) Λ I  = ~ letI-⊗c2 Γ Δ Λ f g  
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ _ ∷ Δ ++ _ ∷ Γ₀) {Δ'} {A} refl (⊗cIc {Γ = Γ} {Δ} {.(Γ₀ ++ A ∷ Δ')} {J = J}{J'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Δ ++ I ∷ Γ₀) Γ Δ' A | cases++-inj₂ (J ⊗ J' ∷ Δ ++ Γ₀) Γ Δ' A | cases++-inj₂ (I ∷ Γ₀) (Γ ++ J ∷ J' ∷ Δ) Δ' A = ⊗cIc {Γ = Γ}{Δ}{Γ₀ ++ asCxt S Γ₁ ++ Δ'}
    cong-ccut2 Δ₀ {Δ'} r (ufIc2 {Γ}{Δ}) with cases++ Δ₀ (_ ∷ Γ) Δ' (I ∷ Δ) r
    cong-ccut2 {nothing} [] {.(Γ₀ ++ I ∷ Δ)} {f = f} refl (ufIc2 {.Γ₀} {Δ} {f = f₁}) | inj₁ (Γ₀ , refl , refl) = scut-Ic Γ₀ Δ f f₁
    cong-ccut2 {just x} {Γ = Γ} [] {.(Γ₀ ++ I ∷ Δ)} {f = f} refl (ufIc2 {.Γ₀} {Δ} {f = f₁}) | inj₁ (Γ₀ , refl , refl) = uf (scut-Ic Γ₀ Δ f f₁) ∙ ufIc2 {Γ = Γ ++ Γ₀}
    cong-ccut2 {S}{Γ = Γ} (x ∷ Δ₀) {.(Γ₀ ++ I ∷ Δ)} {A} refl (ufIc2 {.(Δ₀ ++ A ∷ Γ₀)} {Δ}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (I ∷ Δ) A = ufIc2 {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀}
    cong-ccut2 .(_ ∷ Γ) {.Δ} {f = f₁} refl (ufIc2 {Γ} {Δ} {f = f}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Γ Δ I = ~ letI-uf Γ Δ f₁ f
    cong-ccut2 .(_ ∷ Γ ++ I ∷ Γ₀) {Δ'} {A} refl (ufIc2 {Γ} {.(Γ₀ ++ A ∷ Δ')}) | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀) Γ Δ' A = ufIc2
    cong-ccut2 Δ₀ {Δ'} r (IlIc {Γ} {Δ}) with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    cong-ccut2 {S} {Γ = Γ} Δ₀ {.(Γ₀ ++ I ∷ Δ)} refl (IlIc {.(Δ₀ ++ _ ∷ Γ₀)} {Δ}) | inj₁ (Γ₀ , refl , refl) = IlIc {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀}
    cong-ccut2 Δ₀ {.Δ} {f = f} refl (IlIc {.Δ₀} {Δ} {f = f₁}) | inj₂ ([] , refl , refl) = ~ letI-Il Δ₀ Δ f f₁
    cong-ccut2 {S} {Γ = Γ₁} .(Γ ++ I ∷ Γ₀) {Δ'} refl (IlIc {Γ} {.(Γ₀ ++ _ ∷ Δ')}) | inj₂ (.I ∷ Γ₀ , refl , refl) = IlIc 
    cong-ccut2 Δ₀ {Δ'} r (⊗lIc {Γ} {Δ}) with cases++ Δ₀ Γ Δ' (I ∷ Δ) r
    cong-ccut2 {S} {Γ = Γ} Δ₀ {.(Γ₀ ++ I ∷ Δ)} {A} refl (⊗lIc {.(Δ₀ ++ A ∷ Γ₀)} {Δ}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (I ∷ Δ) A = ⊗lIc {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀}
    cong-ccut2 Δ₀ {.Δ} {f = f} refl (⊗lIc {.Δ₀} {Δ} {f = f₁}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Δ₀ Δ I = ~ letI-⊗l Δ₀ Δ f f₁
    cong-ccut2 .(Γ ++ I ∷ Γ₀) {Δ'} {A} refl (⊗lIc {Γ} {.(Γ₀ ++ _ ∷ Δ')}) | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀) Γ Δ' A = ⊗lIc
    cong-ccut2 Δ₀ {Δ'} r (⊗rIc1 {Γ = Γ} {Γ'} {Δ}) with cases++ Δ₀ Γ Δ' (I ∷ Γ' ++ Δ) r
    cong-ccut2 {S} {Γ = Γ} Δ₀ {.(Γ₀ ++ I ∷ Γ' ++ Δ)} {A} refl (⊗rIc1 {Γ = .(Δ₀ ++ A ∷ Γ₀)} {Γ'} {Δ}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Γ₀ ++ I ∷ Γ') Δ A | cases++-inj₁ Δ₀ (Γ₀ ++ Γ') Δ A | cases++-inj₁ Δ₀ Γ₀ (I ∷ Γ') A = ⊗rIc1 {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀}
    cong-ccut2 Δ₀ {.(Γ' ++ Δ)} {f = f₁} refl (⊗rIc1 {Γ = _} {Γ'} {Δ} {f = f}{g}) | inj₂ ([] , refl , refl) 
     rewrite cases++-inj₁ Δ₀ Γ' Δ I | cases++-inj₂ [] Δ₀ Γ' I = ~ letI-⊗r1 Δ₀ Γ' f₁ f g
    cong-ccut2 _ {Δ'} r (⊗rIc1 {Γ = Γ} {Γ'} {Δ}) | inj₂ (A ∷ Γ₀ , p , refl) with cases++ Γ₀ Γ' Δ' Δ (proj₂ (inj∷ p))
    cong-ccut2 .(Γ ++ I ∷ Γ₀) {.(Γ₀' ++ Δ)} {A} refl (⊗rIc1 {Γ = Γ} {.(Γ₀ ++ A ∷ Γ₀')} {Δ}) | inj₂ (.I ∷ Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ (Γ ++ I ∷ Γ₀) Γ₀' Δ A | cases++-inj₁ (Γ ++ Γ₀) Γ₀' Δ A | cases++-inj₂ (I ∷ Γ₀) Γ Γ₀' A = ⊗rIc1 
    cong-ccut2 .(Γ ++ I ∷ Γ' ++ Γ₀') {Δ'} {A} refl (⊗rIc1 {Γ = Γ} {Γ'} {.(Γ₀' ++ A ∷ Δ')}) | inj₂ (.I ∷ .(Γ' ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
      rewrite cases++-inj₂ Γ₀' (Γ ++ I ∷ Γ') Δ' A | cases++-inj₂ Γ₀' (Γ ++ Γ') Δ' A = ⊗rIc1
    cong-ccut2 Δ₀ {Δ'} r (⊗rIc2 {Γ = Γ} {Δ} {Δ''}) with cases++ Δ₀ (Γ ++ Δ) Δ' (I ∷ Δ'') r
    cong-ccut2 Δ₀ {.(Γ₀ ++ I ∷ Δ'')} r (⊗rIc2 {Γ = Γ} {Δ} {Δ''}) | inj₁ (Γ₀ , p , refl) with cases++ Δ₀ Γ Γ₀ Δ p
    cong-ccut2 Δ₀ {.((Γ₀' ++ Δ) ++ I ∷ Δ'')} {A} refl (⊗rIc2 {Γ = .(Δ₀ ++ A ∷ Γ₀')} {Δ} {Δ''}) | inj₁ (.(Γ₀' ++ Δ) , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (Δ ++ I ∷ Δ'') A | cases++-inj₁ Δ₀ Γ₀' (Δ ++ Δ'') A = ⊗rIc2
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ Γ₀') {.(Γ₀ ++ I ∷ Δ'')} {A} refl (⊗rIc2 {Γ = Γ} {.(Γ₀' ++ _ ∷ Γ₀)} {Δ''}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl)
      rewrite cases++-inj₂ Γ₀' Γ (Γ₀ ++ I ∷ Δ'') A | cases++-inj₂ Γ₀' Γ (Γ₀ ++ Δ'') A | cases++-inj₁ Γ₀' Γ₀ (I ∷ Δ'') A = ⊗rIc2 {Γ = Γ}{Γ₀' ++ asCxt S Γ₁ ++ Γ₀}
    cong-ccut2 .(Γ ++ Δ) {.Δ''} {A} {f = f₁} refl (⊗rIc2 {Γ = Γ} {Δ} {Δ''} {f = f}{g}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ Δ Γ Δ'' I | cases++-inj₂ [] Δ Δ'' I = ~ letI-⊗r2 Δ Δ'' f₁ f g
    cong-ccut2 .(Γ ++ Δ ++ I ∷ Γ₀) {Δ'} {A} refl (⊗rIc2 {Γ = Γ} {Δ} {.(Γ₀ ++ _ ∷ Δ')}) | inj₂ (.I ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (Δ ++ I ∷ Γ₀) Γ Δ' A | cases++-inj₂ (Δ ++ Γ₀) Γ Δ' A | cases++-inj₂ (I ∷ Γ₀) Δ Δ' A = ⊗rIc2
    cong-ccut2 Δ₀ {Δ'} r (⊗c Γ Δ p _ _) with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    cong-ccut2 {S}{Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} refl (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ _ _ p) | inj₁ (Γ₀ , refl , refl) = ⊗c (Δ₀ ++ asCxt S Γ ++ Γ₀) Δ _ _ ( cong-ccut2 Δ₀ refl p )
    cong-ccut2 .Γ {.Δ} {f = f} refl (⊗c Γ Δ _ _ p) | inj₂ ([] , refl , refl) = cong-let⊗2 Γ Δ f p
    cong-ccut2 {S} {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} refl (⊗c Γ .(Γ₀ ++ _ ∷ Δ') _ _ p) | inj₂ (_ ∷ Γ₀ , refl , refl) = ⊗c Γ (Γ₀ ++ asCxt S Γ₁ ++ Δ') _ _ (cong-ccut2 (Γ ++ _ ∷ _ ∷ Γ₀) refl p)
    cong-ccut2 {nothing} [] {Δ'} {f = f} refl (uf⊗c1 {f = f₁}) = ~ let⊗-[] Δ' f f₁
    cong-ccut2 {just x} [] {Δ'} {f = f} refl (uf⊗c1 {f = f₁}) = ~ let⊗-[]-j Δ' f f₁
    cong-ccut2 (_ ∷ Δ₀) refl uf⊗c1 = uf⊗c1
    cong-ccut2 Δ₀ {Δ'} r (⊗c⊗c {Γ = Γ} {Δ} {Λ}) with cases++ Δ₀ (Γ ++ _ ∷ Δ) Δ' (_ ∷ Λ) r
    cong-ccut2 Δ₀ {.(Γ₀ ++ _ ∷ Λ)} r (⊗c⊗c {Γ = Γ} {Δ} {Λ}) | inj₁ (Γ₀ , p , refl) with cases++ Δ₀ Γ Γ₀ (_ ∷ Δ) p
    cong-ccut2 {S}{Γ = Γ} Δ₀ {.((Γ₀' ++ _ ∷ Δ) ++ _ ∷ Λ)} {A} refl (⊗c⊗c {Γ = .(Δ₀ ++ A ∷ Γ₀')} {Δ} {Λ} {J = J}{J'}{K}{K'}) | inj₁ (.(Γ₀' ++ _ ∷ Δ) , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Δ ++ K ⊗ K' ∷ Λ)  A | cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Δ ++ K ∷ K' ∷ Λ) A | cases++-inj₁ Δ₀ (Γ₀' ++ J ∷ J' ∷ Δ) (K ⊗ K' ∷ Λ) A =
      ⊗c⊗c {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀'}{Δ}{Λ}
    cong-ccut2 Δ₀ {.(Γ₀ ++ _ ∷ Λ)}  {f = f'} refl (⊗c⊗c {Γ = .Δ₀} {.Γ₀} {Λ} {J = J}{J'}{K}{K'} {f = f}) | inj₁ (Γ₀ , refl , refl) | inj₂ ([] , refl , refl) 
      rewrite cases++-inj₂ [] Δ₀ (Γ₀ ++ K ⊗ K' ∷ Λ) (J ⊗ J') | cases++-inj₂ [] Δ₀ (Γ₀ ++ K ∷ K' ∷ Λ) (J ⊗ J') = let⊗-⊗c1 Δ₀ Γ₀ Λ f' f
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ _ ∷ Γ₀') {.(Γ₀ ++ _ ∷ Λ)} {A} refl (⊗c⊗c {Γ = Γ} {.(Γ₀' ++ A ∷ Γ₀)} {Λ} {J = J}{J'}{K}{K'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (_ ∷ Γ₀' , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Γ₀ ++ K ⊗ K' ∷ Λ) A | cases++-inj₁ (Γ ++ J ∷ J' ∷ Γ₀') Γ₀ (K ⊗ K' ∷ Λ) A | cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Γ₀ ++ K ∷ K' ∷ Λ) A =
      ⊗c⊗c {Γ = Γ}{Γ₀' ++ asCxt S Γ₁ ++ Γ₀}{Λ}
    cong-ccut2 .(Γ ++ _ ∷ Δ) {.Λ} {f = f} refl (⊗c⊗c {Γ = Γ} {Δ} {Λ} {J = J}{J'}{K}{K'} {f = g}) | inj₂ ([] , refl , refl) 
      rewrite cases++-inj₂ (J ⊗ J' ∷ Δ) Γ Λ (K ⊗ K') | cases++-inj₂ [] (Γ ++ J ∷ J' ∷ Δ) Λ (K ⊗ K')  = ~ let⊗-⊗c2 Γ Δ Λ f g 
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ _ ∷ Δ ++ _ ∷ Γ₀) {Δ'} {A} refl (⊗c⊗c {Γ = Γ} {Δ} {.(Γ₀ ++ A ∷ Δ')} {J = J}{J'}{K}{K'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Δ ++ K ⊗ K' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (J ⊗ J' ∷ Δ ++ K ∷ K' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (K ⊗ K' ∷ Γ₀) (Γ ++ J ∷ J' ∷ Δ) Δ' A =
      ⊗c⊗c {Γ = Γ}{Δ}{Γ₀ ++ asCxt S Γ₁ ++ Δ'}
    cong-ccut2 Δ₀ {Δ'} r (Ic⊗c {Γ = Γ} {Δ} {Λ}) with cases++ Δ₀ (Γ ++ _ ∷ Δ) Δ' (_ ∷ Λ) r
    cong-ccut2 Δ₀ {.(Γ₀ ++ _ ∷ Λ)} r (Ic⊗c {Γ = Γ} {Δ} {Λ} {J = J}{J'}) | inj₁ (Γ₀ , p , refl) with cases++ Δ₀ Γ Γ₀ (_ ∷ Δ) p
    cong-ccut2 {S}{Γ = Γ} Δ₀ {.((Γ₀' ++ _ ∷ Δ) ++ _ ∷ Λ)} {A} refl (Ic⊗c {Γ = .(Δ₀ ++ A ∷ Γ₀')} {Δ} {Λ} {J = J}{J'}) | inj₁ (.(Γ₀' ++ _ ∷ Δ) , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (I ∷ Δ ++ J ⊗ J' ∷ Λ)  A | cases++-inj₁ Δ₀ Γ₀' (I ∷ Δ ++ J ∷ J' ∷ Λ) A | cases++-inj₁ Δ₀ (Γ₀' ++ Δ) (J ⊗ J' ∷ Λ) A = Ic⊗c {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀'}{Δ}{Λ}
    cong-ccut2 Δ₀ {.(Γ₀ ++ _ ∷ Λ)}  {f = f'} refl (Ic⊗c {Γ = .Δ₀} {.Γ₀} {Λ} {J = J}{J'} {f = f}) | inj₁ (Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Δ₀ (Γ₀ ++ J ⊗ J' ∷ Λ) I | cases++-inj₂ [] Δ₀ (Γ₀ ++ J ∷ J' ∷ Λ) I = letI-⊗c1 Δ₀ Γ₀ Λ f' f
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ _ ∷ Γ₀') {.(Γ₀ ++ _ ∷ Λ)} {A} refl (Ic⊗c {Γ = Γ} {.(Γ₀' ++ A ∷ Γ₀)} {Λ} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (_ ∷ Γ₀' , refl , refl)
      rewrite cases++-inj₂ (I ∷ Γ₀') Γ (Γ₀ ++ J ⊗ J' ∷ Λ) A | cases++-inj₁ (Γ ++ Γ₀') Γ₀ (J ⊗ J' ∷ Λ) A | cases++-inj₂ (I ∷ Γ₀') Γ (Γ₀ ++ J ∷ J' ∷ Λ) A = Ic⊗c {Γ = Γ}{Γ₀' ++ asCxt S Γ₁ ++ Γ₀}{Λ} 
    cong-ccut2 .(Γ ++ _ ∷ Δ) {.Λ} {f = f} refl (Ic⊗c {Γ = Γ} {Δ} {Λ} {J = J}{J'} {f = g}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ (I ∷ Δ) Γ Λ (J ⊗ J') | cases++-inj₂ [] (Γ ++ Δ) Λ (J ⊗ J')  = ~ let⊗-Ic2 Γ Δ Λ f g   
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ _ ∷ Δ ++ _ ∷ Γ₀) {Δ'} {A} refl (Ic⊗c {Γ = Γ} {Δ} {.(Γ₀ ++ A ∷ Δ')} {J = J}{J'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (I ∷ Δ ++ J ⊗ J' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (I ∷ Δ ++ J ∷ J' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Γ ++ Δ) Δ' A = Ic⊗c {Γ = Γ}{Δ}{Γ₀ ++ asCxt S Γ₁ ++ Δ'}
    cong-ccut2 Δ₀ {Δ'} r (uf⊗c2 {Γ}{Δ}) with cases++ Δ₀ (_ ∷ Γ) Δ' (_ ∷ Δ) r
    cong-ccut2 {nothing} [] {.(Γ₀ ++ _ ∷ Δ)} {f = f} refl (uf⊗c2 {.Γ₀} {Δ} {f = f₁}) | inj₁ (Γ₀ , refl , refl) = scut-⊗c Γ₀ Δ f f₁
    cong-ccut2 {just x} {Γ = Γ} [] {.(Γ₀ ++ _ ∷ Δ)} {f = f} refl (uf⊗c2 {.Γ₀} {Δ} {f = f₁}) | inj₁ (Γ₀ , refl , refl) = uf (scut-⊗c Γ₀ Δ f f₁) ∙ uf⊗c2 {Γ = Γ ++ Γ₀}
    cong-ccut2 {S}{Γ = Γ} (x ∷ Δ₀) {.(Γ₀ ++ _ ∷ Δ)} {A} refl (uf⊗c2 {.(Δ₀ ++ A ∷ Γ₀)} {Δ} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Δ) A = uf⊗c2 {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀}
    cong-ccut2 .(_ ∷ Γ) {.Δ} {f = f₁} refl (uf⊗c2 {Γ} {Δ} {J = J}{J'} {f = f}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Γ Δ (J ⊗ J') = ~ let⊗-uf Γ Δ f₁ f
    cong-ccut2 .(_ ∷ Γ ++ _ ∷ Γ₀) {Δ'} {A} refl (uf⊗c2 {Γ} {.(Γ₀ ++ A ∷ Δ')} {J = J}{J'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ Δ' A = uf⊗c2
    cong-ccut2 Δ₀ {Δ'} r (Il⊗c {Γ} {Δ}) with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    cong-ccut2 {S} {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} refl (Il⊗c {.(Δ₀ ++ _ ∷ Γ₀)} {Δ}) | inj₁ (Γ₀ , refl , refl) = Il⊗c {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀}
    cong-ccut2 Δ₀ {.Δ} {f = f₁} refl (Il⊗c {.Δ₀} {Δ} {f = f}) | inj₂ ([] , refl , refl) = ~ let⊗-Il Δ₀ Δ f₁ f
    cong-ccut2 {S} {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} refl (Il⊗c {Γ} {.(Γ₀ ++ _ ∷ Δ')}) | inj₂ (_ ∷ Γ₀ , refl , refl) = Il⊗c 
    cong-ccut2 Δ₀ {Δ'} r (⊗l⊗c {Γ} {Δ}) with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    cong-ccut2 {S} {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} {A} refl (⊗l⊗c {.(Δ₀ ++ A ∷ Γ₀)} {Δ} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Δ) A = ⊗l⊗c {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀}
    cong-ccut2 Δ₀ {.Δ} {f = f₁} refl (⊗l⊗c {.Δ₀} {Δ} {J = J}{J'} {f = f}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Δ₀ Δ (J ⊗ J') = ~ let⊗-⊗l Δ₀ Δ f₁ f
    cong-ccut2 .(Γ ++ _ ∷ Γ₀) {Δ'} {A} refl (⊗l⊗c {Γ} {.(Γ₀ ++ _ ∷ Δ')} {J = J}{J'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ Δ' A = ⊗l⊗c
    cong-ccut2 Δ₀ {Δ'} r (⊗r⊗c1 {Γ = Γ} {Γ'} {Δ}) with cases++ Δ₀ Γ Δ' (_ ∷ Γ' ++ Δ) r
    cong-ccut2 {S} {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Γ' ++ Δ)} {A} refl (⊗r⊗c1 {Γ = .(Δ₀ ++ A ∷ Γ₀)} {Γ'} {Δ} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Γ₀ ++ J ⊗ J' ∷ Γ') Δ A | cases++-inj₁ Δ₀ (Γ₀ ++ J ∷ J' ∷ Γ') Δ A | cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Γ') A = ⊗r⊗c1 {Γ = Δ₀ ++ asCxt S Γ ++ Γ₀}
    cong-ccut2 Δ₀ {.(Γ' ++ Δ)} {f = f} refl (⊗r⊗c1 {Γ = _} {Γ'} {Δ}  {J = J}{J'} {f = f₁}{g}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ' Δ (J ⊗ J') | cases++-inj₂ [] Δ₀ Γ' (J ⊗ J') = ~ let⊗-⊗r1 Δ₀ Γ' f f₁ g
    cong-ccut2 _ {Δ'} r (⊗r⊗c1 {Γ = Γ} {Γ'} {Δ}  {J = J}{J'}) | inj₂ (A ∷ Γ₀ , p , refl) with cases++ Γ₀ Γ' Δ' Δ (proj₂ (inj∷ p))
    cong-ccut2 .(Γ ++ _ ∷ Γ₀) {.(Γ₀' ++ Δ)} {A} refl (⊗r⊗c1 {Γ = Γ} {.(Γ₀ ++ A ∷ Γ₀')} {Δ}  {J = J}{J'}) | inj₂ (_ ∷ Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ (Γ ++ J ⊗ J' ∷ Γ₀) Γ₀' Δ A | cases++-inj₁ (Γ ++ J ∷ J' ∷ Γ₀) Γ₀' Δ A | cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ Γ₀' A = ⊗r⊗c1 
    cong-ccut2 .(Γ ++ _ ∷ Γ' ++ Γ₀') {Δ'} {A} refl (⊗r⊗c1 {Γ = Γ} {Γ'} {.(Γ₀' ++ A ∷ Δ')} {J = J}{J'}) | inj₂ (_ ∷ .(Γ' ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
      rewrite cases++-inj₂ Γ₀' (Γ ++ J ⊗ J' ∷ Γ') Δ' A | cases++-inj₂ Γ₀' (Γ ++ J ∷ J' ∷ Γ') Δ' A = ⊗r⊗c1
    cong-ccut2 Δ₀ {Δ'} r (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {J = J}{J'}) with cases++ Δ₀ (Γ ++ Δ) Δ' (_ ∷ Δ'') r
    cong-ccut2 Δ₀ {.(Γ₀ ++ _ ∷ Δ'')} r (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {J = J}{J'}) | inj₁ (Γ₀ , p , refl) with cases++ Δ₀ Γ Γ₀ Δ p
    cong-ccut2 Δ₀ {.((Γ₀' ++ Δ) ++ _ ∷ Δ'')} {A} refl (⊗r⊗c2 {Γ = .(Δ₀ ++ A ∷ Γ₀')} {Δ} {Δ''} {J = J}{J'}) | inj₁ (.(Γ₀' ++ Δ) , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (Δ ++ J ⊗ J' ∷ Δ'') A | cases++-inj₁ Δ₀ Γ₀' (Δ ++ J ∷ J' ∷ Δ'') A = ⊗r⊗c2
    cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ Γ₀') {.(Γ₀ ++ _ ∷ Δ'')} {A} refl (⊗r⊗c2 {Γ = Γ} {.(Γ₀' ++ _ ∷ Γ₀)} {Δ''} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl)
      rewrite cases++-inj₂ Γ₀' Γ (Γ₀ ++ J ⊗ J' ∷ Δ'') A | cases++-inj₂ Γ₀' Γ (Γ₀ ++ J ∷ J' ∷ Δ'') A | cases++-inj₁ Γ₀' Γ₀ (J ⊗ J' ∷ Δ'') A = ⊗r⊗c2 {Γ = Γ}{Γ₀' ++ asCxt S Γ₁ ++ Γ₀}
    cong-ccut2 .(Γ ++ Δ) {.Δ''} {A} {f = f} refl (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {J = J}{J'} {f = f₁}{g}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ Δ Γ Δ'' (J ⊗ J') | cases++-inj₂ [] Δ Δ'' (J ⊗ J') = ~ let⊗-⊗r2 Δ Δ'' f f₁ g
    cong-ccut2 .(Γ ++ Δ ++ _ ∷ Γ₀) {Δ'} {A} refl (⊗r⊗c2 {Γ = Γ} {Δ} {.(Γ₀ ++ _ ∷ Δ')} {J = J}{J'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (Δ ++ J ⊗ J' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (Δ ++ J ∷ J' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (J ⊗ J' ∷ Γ₀) Δ Δ' A = ⊗r⊗c2

cong-scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
             {f g : S ∣ Γ ⊢ A}  → {h k : just A ∣ Δ' ⊢ C} →
             f ≗ g → h ≗ k → scut f h ≗ scut g k
cong-scut {g = g} p q = cong-scut1 p ∙ cong-scut2 g q             

cong-ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
             {f f' : nothing ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C}  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
             f ≗ f' → g ≗ g' → ccut Δ₀ f g r ≗ ccut Δ₀ f' g' r
cong-ccut Δ₀ {g = g} r p q = cong-ccut1 Δ₀ g r p  ∙ cong-ccut2 Δ₀ r q
