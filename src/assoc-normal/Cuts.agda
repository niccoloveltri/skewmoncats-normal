{-# OPTIONS --rewriting #-}

module Cuts where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.Bool
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

-- An admissible left-rule for I, which allow to remove I from the
-- passive context when there exist a formula directly to its right.

Ic : {S : Stp} (Γ Λ : Cxt) {Γ' : Cxt} {A C : Fma}
  → S ∣ Γ' ⊢ C → Γ' ≡ Γ ++ A ∷ Λ
  → S ∣ Γ ++ I ∷ A ∷ Λ ⊢ C
Ic Γ _ ax eq =  ⊥-elim ([]disj∷ Γ eq)
Ic Γ _ (uf f) eq with cases∷ Γ eq
Ic [] _ (uf f) eq | inj₁ (refl , refl , refl) = uf (Il (uf f))
Ic .(_ ∷ Γ₀) _ (uf f) eq | inj₂ (Γ₀ , refl , refl) = uf (Ic Γ₀ _ f refl)
Ic Γ _ Ir eq = ⊥-elim ([]disj∷ Γ eq)
Ic Γ Λ (⊗r {Γ = Γ₁} {Δ} f g) eq with cases++ Γ Γ₁ Λ Δ eq
Ic Γ _ (⊗r {Γ = .(Γ ++ _ ∷ Γ₀)} {Δ} f g) eq | inj₁ (Γ₀ , refl , refl) =
  ⊗r (Ic Γ Γ₀ f refl) g
Ic _ Λ (⊗r {Γ = Γ₁} {.(Γ₀ ++ _ ∷ Λ)} f g) eq | inj₂ (Γ₀ , refl , refl) =
  ⊗r f (Ic Γ₀ Λ g refl)
Ic Γ Λ (Il f) eq = Il (Ic Γ Λ f eq)
Ic Γ Λ (⊗l f) refl = ⊗l (Ic (_ ∷ Γ) Λ f refl)
Ic Γ₁ Λ (⊗c Γ Δ {A} {B} f) eq with cases++ Γ₁ Γ Λ (A ⊗ B ∷ Δ) eq
Ic Γ₁ _ (⊗c .(Γ₁ ++ _ ∷ Γ₀) Δ {A} {B} f) eq | inj₁ (Γ₀ , refl , refl) =
  ⊗c (Γ₁ ++ I ∷ _ ∷ Γ₀) Δ (Ic Γ₁ (Γ₀ ++ A ∷ B ∷ Δ) f refl)
Ic _ _ (⊗c Γ Δ {A} {B} f) eq | inj₂ ([] , refl , refl) = ⊗c (Γ ++ I ∷ []) Δ (Ic Γ (B ∷ Δ) f refl)
Ic _ Λ (⊗c Γ .(Γ₀ ++ _ ∷ Λ) {A} {B} f) eq | inj₂ (.(A ⊗ B) ∷ Γ₀ , refl , refl) =
  ⊗c Γ (Γ₀ ++ I ∷ _ ∷ Λ) (Ic (Γ ++ A ∷ B ∷ Γ₀) Λ f refl)

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
  scut Ir (⊗c Γ Δ g) = ⊗c Γ Δ (scut Ir g)
  scut (⊗r f f₁) ax = ⊗r f f₁
  scut (⊗r f f₁) (⊗r g g₁) = ⊗r (scut (⊗r f f₁) g) g₁
  scut (⊗r f f₁) (⊗l g) = scut f (ccut false [] f₁ g refl)
  scut (⊗r {Γ = Γ₁} {Δ₁} f f₁) (⊗c Γ Δ g) = ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ (scut (⊗r f f₁) g)
  scut (Il f) g = Il (scut f g)
  scut (⊗l f) g = ⊗l (scut f g)
  scut {Δ' = Δ'} (⊗c Γ Δ f) g = ⊗c Γ (Δ ++ Δ') (scut f g)
  
  ccut : (b : Bool) {T S : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             T ∣ Γ ⊢ A  →  S ∣ Δ ⊢ C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        S ∣ Δ₀ ++ asCxt b T Γ ++ Δ' ⊢ C
  ccut b Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut b Δ₀ f (uf g) p with cases∷ Δ₀ p 
  ccut b {just A} .[] f (uf g) p | inj₁ (refl , refl , refl) = uf (scut f g)  
  ccut false {nothing} .[] f (uf g) p | inj₁ (refl , refl , refl) = scut f g
  ccut true {nothing} .[] f (uf g) p | inj₁ (refl , refl , refl) = uf (Il (scut f g))
  ccut b .(_ ∷ Δ₀) f (uf g) p | inj₂ (Δ₀ , r , refl) =  uf (ccut b Δ₀ f g r)
  ccut b Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut b Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
  ccut b Δ₀ f (⊗r g g') p | inj₁ (Γ₀ , refl , refl) = ⊗r (ccut b Δ₀ f g refl) g'
  ccut b ._ f (⊗r g g') p | inj₂ (Γ₀ , refl , refl) = ⊗r g (ccut b Γ₀  f g' refl)
  ccut b Δ₀ f (Il g) r = Il (ccut b Δ₀ f g r)
  ccut b Δ₀ f (⊗l {B = B} g) r = ⊗l (ccut b (B ∷ Δ₀) f g (cong (_∷_ B) r))
  ccut b Δ₀ {Δ'} f (⊗c Γ Δ {J} {J'} g) r with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) r
  ccut b {T} {Γ = Γ} Δ₀ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ {J} {J'} g) r | inj₁ (Γ₀ , refl , refl) =
    ⊗c (Δ₀ ++ asCxt b T Γ ++ Γ₀) Δ  (ccut b Δ₀ f g refl)
  ccut b .Γ {.Δ} f (⊗c Γ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl) = let⊗ b Γ Δ f g
  ccut b {T} {Γ = Γ₁} .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') {J} {J'} g) r | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) =
    ⊗c Γ (Γ₀ ++ asCxt b T Γ₁ ++ Δ') (ccut b (Γ ++ J ∷ J' ∷ Γ₀) f g refl)

  let⊗ : (b : Bool) {T S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {C J J' : Fma}
      → T ∣ Γ ⊢ J ⊗ J' →  S ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C
      → S ∣ Δ₀ ++ asCxt b T Γ ++ Δ₁ ⊢ C
  let⊗ b Δ₀ Δ₁ ax g = ⊗c Δ₀ Δ₁ g
  let⊗ false Δ₀ Δ₁ (uf f) g = let⊗ false Δ₀ Δ₁ f g
  let⊗ true Δ₀ Δ₁ (uf f) g = Ic Δ₀ _ (let⊗ true Δ₀ Δ₁ f g) refl
  let⊗ b Δ₀ Δ₁ (⊗r {Γ = Γ}{Δ} f f₁) g = ccut b Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) f₁ g refl) refl
  let⊗ b Δ₀ Δ₁ (Il f) g = let⊗ true Δ₀ Δ₁ f g
  let⊗ b {Γ = Γ} Δ₀ Δ₁ (⊗l f) g = ⊗c Δ₀ (Γ ++ Δ₁) (let⊗ b Δ₀ Δ₁ f g)
  let⊗ b {T} Δ₀ Δ₁ (⊗c Γ Δ f) g = ⊗c (Δ₀ ++ asCxt b T Γ) (Δ ++ Δ₁) (let⊗ b Δ₀ Δ₁ f g)

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
  scut⊗ruf {Γ₁} {Δ₁} (⊗c Γ Δ f) =
    ⊗c (_ ∷ Γ₁ ++ Δ₁ ++ Γ) Δ (scut⊗ruf f)
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
  scut⊗rIl {Γ₁} {Δ₁} (⊗c Γ Δ h) =
    ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ (scut⊗rIl h)
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
  scut⊗r⊗l {Γ₁} {Δ₁} (⊗c Γ Δ h) = 
    ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ (scut⊗r⊗l h)
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
  scut⊗r {Δ = Δ₁} {Δ'} (⊗c Γ Δ f) g g' = 
    ⊗c Γ (Δ ++ Δ₁ ++ Δ') (scut⊗r f g g')
    ∙ ~ ⊗r⊗c1 

-- -- unitality of identity wrt. cut

abstract
  ccut-unit : {T : Stp}{Γ Δ : Cxt}(Δ₀ : Cxt){A C : Fma}
    → (g : T ∣ Δ ⊢ C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
    → ccut false Δ₀ (uf ax) g r ≡ subst-cxt r g
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
  ccut-unit {Γ = Γ₁} Δ₀ (⊗c Γ Δ g) r with cases++ Δ₀ Γ Γ₁ (_ ⊗ _ ∷ Δ) r
  ccut-unit {Γ = .(Γ₀ ++ _ ⊗ _ ∷ Δ)} Δ₀ (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
    cong (⊗c (Δ₀ ++ _ ∷ Γ₀) Δ) (ccut-unit Δ₀ g refl)
  ccut-unit {Γ = .Δ} .Γ (⊗c Γ Δ {J = J}{J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ Δ (J ⊗ J') = refl
  ccut-unit {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) (⊗c Γ .(Γ₀ ++ _ ∷ Γ₁) g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    cong (⊗c Γ (Γ₀ ++ _ ∷ Γ₁)) (ccut-unit (Γ ++ _ ∷ _ ∷ Γ₀) g refl)
  
  scut-unit : {S : Stp}{Γ : Cxt}{A : Fma}(f : S ∣ Γ ⊢ A) → scut f ax ≡ f
  scut-unit ax = refl
  scut-unit (uf f) = cong uf (scut-unit f)
  scut-unit Ir = refl
  scut-unit (⊗r f f') = refl
  scut-unit (Il f) = cong Il (scut-unit f)
  scut-unit (⊗l f) = cong ⊗l (scut-unit f)
  scut-unit (⊗c Γ Δ f) = cong (⊗c Γ Δ) (scut-unit f)

-- ====================================================================

-- the cut rules, also Ic and let⊗, commute with Il-1 and ⊗-1

abstract
  Ic-Il-1 : (Γ Λ : Cxt) {Γ' : Cxt} {A C : Fma}
    → (f : just I ∣ Γ' ⊢ C) (eq : Γ' ≡ Γ ++ A ∷ Λ)
    → Ic Γ Λ (Il-1 f) eq ≡ Il-1 (Ic Γ Λ f eq)
  Ic-Il-1 Γ Λ ax eq = ⊥-elim ([]disj∷ Γ eq)
  Ic-Il-1 Γ Λ (⊗r {Γ = Γ₁} {Δ} f f₁) eq with cases++ Γ Γ₁ Λ Δ eq
  Ic-Il-1 Γ .(Γ₀ ++ Δ) (⊗r {Γ = .(Γ ++ _ ∷ Γ₀)} {Δ} f f₁) eq | inj₁ (Γ₀ , refl , refl) =
    cong (λ x → ⊗r {Γ = Γ ++ I ∷ _ ∷ Γ₀} x f₁) (Ic-Il-1 Γ Γ₀ f refl)
  Ic-Il-1 .(Γ₁ ++ Γ₀) Λ (⊗r {Γ = Γ₁} {.(Γ₀ ++ _ ∷ Λ)} f f₁) eq | inj₂ (Γ₀ , refl , refl) = refl
  Ic-Il-1 Γ Λ (Il f) eq = refl
  Ic-Il-1 Γ Λ (⊗c Γ₁ Δ f) eq with cases++ Γ Γ₁ Λ (_ ∷ Δ) eq
  Ic-Il-1 Γ .(Γ₀ ++ _ ⊗ _ ∷ Δ) (⊗c .(Γ ++ _ ∷ Γ₀) Δ f) eq | inj₁ (Γ₀ , refl , refl) =
    cong (⊗c (Γ ++ I ∷ _ ∷ Γ₀) Δ) (Ic-Il-1 Γ (Γ₀ ++ _ ∷ _ ∷ Δ) f refl)
  Ic-Il-1 .Γ₁ .Δ (⊗c Γ₁ Δ f) eq | inj₂ ([] , refl , refl) =
    cong (⊗c (Γ₁ ++ _ ∷ []) Δ) (Ic-Il-1 Γ₁ (_ ∷ Δ) f refl)
  Ic-Il-1 .(Γ₁ ++ _ ⊗ _ ∷ Γ₀) Λ (⊗c Γ₁ .(Γ₀ ++ _ ∷ Λ) f) eq | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    cong (⊗c Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ)) (Ic-Il-1 (Γ₁ ++ _ ∷ _ ∷ Γ₀) Λ f refl)
  
  mutual
    ccut-Il-1 : ∀{b : Bool}{T}{Γ}{Δ}{A}{C} Δ₀ {Δ'}
      → (f : T ∣ Γ ⊢ A)(g : just I ∣ Δ ⊢ C)
      → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
      → Il-1 (ccut b Δ₀ f g r) ≡ ccut b Δ₀ f (Il-1 g) r
    ccut-Il-1 Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-Il-1 {Γ = Γ} Δ₀ {Δ'} f (⊗r {Γ = Γ'}{Δ} g g') r with cases++ Δ₀ Γ' Δ' Δ r
    ccut-Il-1 {b}{T}{Γ} Δ₀ {_} f (⊗r {Γ = _} {Δ} g g') r | inj₁ (Γ₀ , refl , refl) = 
      cong₂ (⊗r {Γ = Δ₀ ++ asCxt b T Γ ++ Γ₀}{Δ}) (ccut-Il-1 Δ₀  f g refl) refl
    ccut-Il-1 ._ f (⊗r g g') r | inj₂ (Γ₀ , refl , refl) = refl
    ccut-Il-1 Δ₀ f (Il g) r = refl
    ccut-Il-1 Δ₀ {Δ'} f (⊗c Γ Δ g) r with cases++ Δ₀ Γ Δ' (_ ⊗ _ ∷ Δ) r
    ccut-Il-1 {b}{T}{Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
      cong (⊗c (Δ₀ ++ asCxt b T Γ ++ Γ₀) Δ) (ccut-Il-1 Δ₀ f g refl)
    ccut-Il-1 .Γ {.Δ} f (⊗c Γ Δ g) refl | inj₂ ([] , refl , refl) = let⊗-Il-1 Γ Δ f g  
    ccut-Il-1 {b}{T}{Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (._ ∷ Γ₀ , refl , refl) =
      cong (⊗c Γ (Γ₀ ++ asCxt b T Γ₁ ++ Δ')) (ccut-Il-1 (Γ ++ _ ∷ _ ∷ Γ₀) f g refl)
      
    let⊗-Il-1 : ∀{b}{T}{Γ}{C J J'} Δ₀ Δ₁ 
      → (f : T ∣ Γ ⊢ J ⊗ J')(g : just I ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ⊢ C)
      → Il-1 (let⊗ b Δ₀ Δ₁ f g) ≡ let⊗ b Δ₀ Δ₁ f (Il-1 g)
    let⊗-Il-1 {false} Δ₀ Δ₁ (uf f) g = let⊗-Il-1 Δ₀ Δ₁ f g
    let⊗-Il-1 {true} Δ₀ Δ₁ (uf {Γ} f) g =
      trans (sym (Ic-Il-1 Δ₀ (Γ ++ Δ₁) (let⊗ true Δ₀ Δ₁ f g) refl))
        (cong (λ x → Ic Δ₀ (Γ ++ Δ₁) x refl) (let⊗-Il-1 Δ₀ Δ₁ f g))
    let⊗-Il-1 {b} Δ₀ Δ₁ (⊗r f f') g =
      trans (ccut-Il-1 Δ₀  f (ccut _ (Δ₀ ++ _ ∷ []) f' g refl) refl)
        (cong (λ x → ccut b Δ₀ f x refl) (ccut-Il-1  (Δ₀ ++ _ ∷ []) f' g refl))
    let⊗-Il-1 {b}{T} Δ₀ Δ₁ (⊗c Γ Δ f) g = cong (⊗c (Δ₀ ++ asCxt b T Γ) (Δ ++ Δ₁)) (let⊗-Il-1 Δ₀ Δ₁ f g)
    let⊗-Il-1 Δ₀ Δ₁ ax g = refl
    let⊗-Il-1 {b}{T}{Γ} Δ₀ Δ₁ (⊗l f) g = cong (⊗c Δ₀ (Γ ++ Δ₁)) (let⊗-Il-1 Δ₀ Δ₁ f g)
    let⊗-Il-1 Δ₀ Δ₁ (Il f) g = let⊗-Il-1 Δ₀ Δ₁ f g

abstract
  Il-1-scutIr : {Γ : Cxt} → {C : Fma}
    → (f : just I ∣ Γ ⊢ C)
    → Il-1 f ≡ scut Ir f
  Il-1-scutIr ax = refl
  Il-1-scutIr (⊗r {Γ = Γ} {Δ} f f₁) =
    cong₂ (⊗r {Γ = Γ} {Δ}) (Il-1-scutIr f) refl
  Il-1-scutIr (Il f) = refl
  Il-1-scutIr (⊗c Γ Δ f) = cong (⊗c Γ Δ) (Il-1-scutIr f)

  scutIl-1 : {Γ Δ : Cxt} → {A C : Fma}
    → (f : just I ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ C)
    → Il-1 (scut f g) ≡ scut (Il-1 f) g
  scutIl-1 ax g = Il-1-scutIr g
  scutIl-1 (⊗r f f') ax = refl
  scutIl-1 (⊗r {Γ = Γ} {Δ} f f') (⊗r {Γ = Γ₁} {Δ₁} g g') =
    cong₂ (⊗r {Γ = Γ ++ Δ ++ Γ₁}{Δ₁}) (scutIl-1 (⊗r f f') g) refl
  scutIl-1 (⊗r {Γ = Γ} f f') (⊗l g) = scutIl-1 f (ccut _ [] f' g refl)
  scutIl-1 (⊗r {Γ = Γ} {Δ} f f') (⊗c Γ' Δ' g) =
    cong (⊗c (Γ ++ Δ ++ Γ') Δ') (scutIl-1 (⊗r f f') g)
  scutIl-1 (Il f) g = refl
  scutIl-1 {Δ = Δ₁} (⊗c Γ Δ f) g = cong (⊗c Γ (Δ ++ Δ₁)) (scutIl-1 f g)



abstract
  ⊗l-1-scut⊗r : {Γ : Cxt} → {A B C : Fma}
    → (f : just (A ⊗ B) ∣ Γ ⊢ C)
    → ⊗l-1 f ≡ scut (⊗r ax (uf ax)) f
  ⊗l-1-scut⊗r ax = refl
  ⊗l-1-scut⊗r (⊗r {Γ = Γ} {Δ} f f₁) = cong₂ (⊗r {Γ = _ ∷ Γ}{Δ}) (⊗l-1-scut⊗r f) refl
  ⊗l-1-scut⊗r (⊗l f) = sym (ccut-unit [] f refl)  
  ⊗l-1-scut⊗r (⊗c Γ Δ f) = cong (⊗c (_ ∷ Γ) Δ) (⊗l-1-scut⊗r f)


-- Lots of permutation laws  
  
  ccut-⊗c : {b : Bool}{S T : Stp} → {Δ : Cxt} → (Δ₀ Γ₁ Γ₂ : Cxt) → {Δ' : Cxt} →  {A C J J' : Fma} → 
               (f : S ∣ Γ₁ ++ J ∷ J' ∷ Γ₂ ⊢ A)(g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
              ccut b Δ₀ (⊗c Γ₁ Γ₂ f) g r ≗ ⊗c (Δ₀ ++ asCxt b S Γ₁) (Γ₂ ++ Δ') (ccut b Δ₀ f g r)
  ccut-⊗c Δ₀ Γ₁ Γ₂ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-⊗c Δ₀ Γ₁ Γ₂ f (uf g) r with cases∷ Δ₀ r
  ccut-⊗c {false} {nothing} .[] Γ₁ Γ₂ f (uf g) refl | inj₁ (refl , refl , refl) = refl
  ccut-⊗c {true} {nothing} .[] Γ₁ Γ₂ f (uf g) refl | inj₁ (refl , refl , refl) =
    uf (Il⊗c) ∙ uf⊗c2
  ccut-⊗c {false} {just A'} .[] Γ₁ Γ₂ f (uf g) refl | inj₁ (refl , refl , refl) = uf⊗c2
  ccut-⊗c {true} {just A'} .[] Γ₁ Γ₂ f (uf g) refl | inj₁ (refl , refl , refl) = uf⊗c2
  ccut-⊗c {b}{S} .(_ ∷ Γ₀) Γ₁ Γ₂ {Δ'} f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
    uf (ccut-⊗c Γ₀ Γ₁ Γ₂ f g refl) ∙ uf⊗c2 {Γ = Γ₀ ++ asCxt b S Γ₁}
  ccut-⊗c Δ₀ Γ₁ Γ₂ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-⊗c Δ₀ Γ₁ Γ₂ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
  ccut-⊗c {b}{S} Δ₀ Γ₁ Γ₂ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) r | inj₁ (Γ₀ , refl , refl) =
    ⊗r (ccut-⊗c Δ₀ Γ₁ Γ₂ f g refl) refl ∙ ⊗r⊗c1 {Γ = Δ₀ ++ asCxt b S Γ₁}
  ccut-⊗c {b}{S} .(Γ ++ Γ₀) Γ₁ Γ₂ {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) r | inj₂ (Γ₀ , refl , refl) =
    ⊗r refl (ccut-⊗c Γ₀ Γ₁ Γ₂ f g₁ refl) ∙ ⊗r⊗c2 {Δ = Γ₀ ++ asCxt b S Γ₁}
  ccut-⊗c {b}{S} Δ₀ Γ₁ Γ₂ f (Il g) refl =
    Il (ccut-⊗c Δ₀ Γ₁ Γ₂ f g refl) ∙ Il⊗c {Γ = Δ₀ ++ asCxt b S Γ₁}
  ccut-⊗c {b}{S} Δ₀ Γ₁ Γ₂ f (⊗l g) refl = 
    ⊗l (ccut-⊗c (_ ∷ Δ₀) Γ₁ Γ₂ f g refl) ∙ ⊗l⊗c {Γ = Δ₀ ++ asCxt b S Γ₁}
  ccut-⊗c Δ₀ Γ₁ Γ₂ {Δ'} f (⊗c Γ Δ g) r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
  ccut-⊗c {b}{S} Δ₀ Γ₁ Γ₂ {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
    ⊗c (Δ₀ ++ asCxt b S Γ₁ ++ _ ∷ Γ₂ ++ Γ₀) Δ (ccut-⊗c Δ₀ Γ₁ Γ₂ f g refl)
    ∙ (~ ⊗c⊗c {Γ = Δ₀ ++ asCxt b S Γ₁}{Γ₂ ++ Γ₀}{Δ})
  ccut-⊗c .Γ Γ₁ Γ₂ {.Δ} f (⊗c Γ Δ g) refl | inj₂ ([] , refl , refl) = refl
  ccut-⊗c {b}{S} .(Γ ++ _ ⊗ _ ∷ Γ₀) Γ₁ Γ₂ {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    ⊗c Γ (Γ₀ ++ asCxt b S Γ₁ ++ _ ∷ Γ₂ ++ Δ') (ccut-⊗c (Γ ++ _ ∷ _ ∷ Γ₀) Γ₁ Γ₂ f g refl)
    ∙ ⊗c⊗c {Γ = Γ}{Γ₀ ++ asCxt b S Γ₁}
  
  scut-⊗c : {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {A C J J' : Fma} → 
              (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C) →
              scut f (⊗c Δ₁ Δ₂ g) ≗ ⊗c (Γ ++ Δ₁) Δ₂ (scut f g)
  scut-⊗c Δ₁ Δ₂ ax g = refl
  scut-⊗c Δ₁ Δ₂ (uf {Γ} f) g =
    uf (scut-⊗c Δ₁ Δ₂ f g) ∙ uf⊗c2 {Γ = Γ ++ Δ₁}{Δ₂}
  scut-⊗c Δ₁ Δ₂ Ir g = refl
  scut-⊗c Δ₁ Δ₂ (⊗r f f₁) g = refl
  scut-⊗c {Γ = Γ} Δ₁ Δ₂ (Il f) g =
    Il (scut-⊗c Δ₁ Δ₂ f g) ∙ Il⊗c {Γ = Γ ++ Δ₁}{Δ₂}
  scut-⊗c {Γ = Γ} Δ₁ Δ₂ (⊗l f) g =
    ⊗l (scut-⊗c Δ₁ Δ₂ f g) ∙ ⊗l⊗c {Γ = Γ ++ Δ₁}{Δ₂}
  scut-⊗c Δ₁ Δ₂ (⊗c Γ Δ f) g =
    ⊗c Γ (Δ ++ Δ₁ ++ _ ∷ Δ₂) (scut-⊗c Δ₁ Δ₂ f g)
    ∙ ⊗c⊗c {Γ = Γ}{Δ ++ Δ₁}{Δ₂}
  
  
  
  ccut-ax : {b : Bool} {T : Stp}{Γ Δ : Cxt}(Δ₀ : Cxt){A C : Fma}
    → (g : T ∣ Δ ⊢ C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
    → ccut b Δ₀ ax g r ≡ subst-cxt r g
  ccut-ax Δ₀ ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ax Δ₀ (uf g) r with cases∷ Δ₀ r
  ccut-ax .[] (uf g) refl | inj₁ (refl , refl , refl) = refl
  ccut-ax .(_ ∷ Γ) (uf g) refl | inj₂ (Γ , refl , refl) = cong uf (ccut-ax Γ g refl)
  ccut-ax Δ₀ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ax {_}{_}{Γ} Δ₀ (⊗r {Γ = Γ'}{Δ} g g') r with cases++ Δ₀ Γ' Γ Δ r
  ccut-ax Δ₀ (⊗r {Γ = Γ}{Δ} g g') refl | inj₁ (Γ₀ , refl , refl) = 
    cong₂ (⊗r {Γ = Γ}{Δ}) (ccut-ax Δ₀ g refl) refl
  ccut-ax ._ (⊗r {Γ = Γ}{Δ} g g') refl | inj₂ (Δ₀ , refl , refl) =
    cong₂ (⊗r {Γ = Γ}) refl (ccut-ax Δ₀ g' refl)
  ccut-ax Δ₀ (Il g) refl = cong Il (ccut-ax Δ₀ g refl)
  ccut-ax Δ₀ (⊗l g) refl = cong ⊗l (ccut-ax (_ ∷ Δ₀) g refl)
  ccut-ax {Γ = Γ₁} Δ₀ (⊗c Γ Δ g) r with cases++ Δ₀ Γ Γ₁ (_ ⊗ _ ∷ Δ) r
  ccut-ax {Γ = .(Γ₀ ++ _ ⊗ _ ∷ Δ)} Δ₀ (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl | inj₁ (Γ₀ , refl , refl) =
    cong (⊗c (Δ₀ ++ _ ∷ Γ₀) Δ) (ccut-ax Δ₀ g refl)
  ccut-ax {Γ = .Δ} .Γ (⊗c Γ Δ {J = J}{J'} g) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ Δ (J ⊗ J') = refl
  ccut-ax {Γ = Γ₁} .(Γ ++ _ ⊗ _ ∷ Γ₀) (⊗c Γ .(Γ₀ ++ _ ∷ Γ₁) g) refl | inj₂ (.(_ ⊗ _) ∷ Γ₀ , refl , refl) =
    cong (⊗c Γ (Γ₀ ++ _ ∷ Γ₁)) (ccut-ax (Γ ++ _ ∷ _ ∷ Γ₀) g refl)
  
  ccut-uf : {S : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' C : Fma} → 
               (f : just A' ∣ Γ ⊢ A)(g : S ∣ Δ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ') → 
          ccut false Δ₀ (uf f) g r ≡ ccut false Δ₀ f g r --ccut b Δ₀ f g r
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
  ccut-uf Δ₀ {Δ'} f (⊗c Γ Δ g) r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
  ccut-uf {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) r | inj₁ (Γ₀ , refl , refl) = 
    cong (⊗c (Δ₀ ++ _ ∷ Γ ++ Γ₀) Δ) (ccut-uf Δ₀ f g refl)
  ccut-uf .Γ {.Δ} f (⊗c Γ Δ g) refl | inj₂ ([] , refl , refl) = refl
  ccut-uf {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') g) r | inj₂ (_ ∷ Γ₀ , refl , refl) = 
    cong (⊗c Γ (Γ₀ ++ _ ∷ Γ₁ ++ Δ')) (ccut-uf (Γ ++ _ ∷ _ ∷ Γ₀) f g refl)

  ccut-uf-true : {S : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' C : Fma} → 
               (f : just A' ∣ Γ ⊢ A)(g : S ∣ Δ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ') → 
          ccut true Δ₀ (uf f) g r ≡ Ic Δ₀ (Γ ++ Δ') (ccut true Δ₀ f g r) refl
  ccut-uf-true Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r) 
  ccut-uf-true Δ₀ f (uf g) r with  cases∷ Δ₀ r
  ccut-uf-true .[] f (uf g) r | inj₁ (refl , refl , refl) = refl
  ccut-uf-true .(_ ∷ Γ₀) f (uf g) r | inj₂ (Γ₀ , refl , refl) = cong uf (ccut-uf-true Γ₀ f g refl)
  ccut-uf-true Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r) 
  ccut-uf-true Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
  ccut-uf-true {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} {A' = A'} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) r | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀) Δ A' = cong (λ x → ⊗r {Γ = Δ₀ ++ _ ∷ _ ∷ Γ ++ Γ₀} x g₁) (ccut-uf-true Δ₀ f g refl)
  ccut-uf-true {Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} {A' = A'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) r | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ (Γ₁ ++ Δ') A' = cong (⊗r g) (ccut-uf-true Γ₀ f g₁ refl)
  ccut-uf-true Δ₀ f (Il g) r = cong Il (ccut-uf-true Δ₀ f g r)
  ccut-uf-true Δ₀ f (⊗l g) refl = cong ⊗l (ccut-uf-true (_ ∷ Δ₀) f g refl)
  ccut-uf-true Δ₀ {Δ'} f (⊗c Γ Δ {J} {J'} g) r with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) r
  ccut-uf-true {Γ = Γ} Δ₀ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} {A' = A'} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ {J} {J'} g) r | inj₁ (Γ₀ , refl , refl) 
    rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀) (J ⊗ J' ∷ Δ) A' =
      cong (⊗c (Δ₀ ++ I ∷ A' ∷ Γ ++ Γ₀) Δ) (ccut-uf-true Δ₀ f g refl)
  ccut-uf-true .Γ {.Δ} f (⊗c Γ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl) = refl
  ccut-uf-true {Γ = Γ₁} .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} {A' = A'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') {J} {J'} g) r | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) 
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (Γ₁ ++ Δ') A' =
    cong (⊗c Γ (Γ₀ ++ I ∷ A' ∷ Γ₁ ++ Δ')) (ccut-uf-true (Γ ++ J ∷ J' ∷ Γ₀) f g refl)


-- Ic is compatible with ≗

  cong-Ic : {S : Stp} (Γ Λ : Cxt) {Γ' : Cxt} {A C : Fma}
     → {f g : S ∣ Γ' ⊢ C} → f ≗ g → (eq : Γ' ≡ Γ ++ A ∷ Λ)
     → Ic Γ Λ f eq ≗ Ic Γ Λ g eq
  cong-Ic Γ Λ refl eq = refl
  cong-Ic Γ Λ (~ p) eq = ~ cong-Ic Γ Λ p eq
  cong-Ic Γ Λ (p ∙ p₁) eq = cong-Ic Γ Λ p eq ∙ cong-Ic Γ Λ p₁ eq
  cong-Ic Γ Λ (uf p) eq with cases∷ Γ eq
  cong-Ic .[] Λ (uf p) eq | inj₁ (refl , refl , refl) = uf (Il (uf p))
  cong-Ic .(_ ∷ Γ₀) Λ (uf p) eq | inj₂ (Γ₀ , refl , refl) = uf (cong-Ic Γ₀ Λ p refl)
  cong-Ic Γ Λ (⊗l p) refl = ⊗l (cong-Ic (_ ∷ Γ) Λ p refl)
  cong-Ic Γ Λ (Il p) eq = Il (cong-Ic Γ Λ p eq)
  cong-Ic Γ Λ (⊗r {Γ = Γ₁} {Δ} p p₁) eq with cases++ Γ Γ₁ Λ Δ eq
  cong-Ic Γ .(Γ₀ ++ Δ) (⊗r {Γ = .(Γ ++ _ ∷ Γ₀)} {Δ} p p₁) eq | inj₁ (Γ₀ , refl , refl) =
    ⊗r (cong-Ic Γ Γ₀ p refl) p₁
  cong-Ic .(Γ₁ ++ Γ₀) Λ (⊗r {Γ = Γ₁} {.(Γ₀ ++ _ ∷ Λ)} p p₁) eq | inj₂ (Γ₀ , refl , refl) =
    ⊗r p (cong-Ic Γ₀ Λ p₁ refl)
  cong-Ic Γ Λ axI eq = ⊥-elim ([]disj∷ Γ eq)
  cong-Ic Γ Λ ax⊗ eq = ⊥-elim ([]disj∷ Γ eq)
  cong-Ic Γ Λ (⊗ruf {Γ₁} {Δ} {A' = A'}) eq with cases++ Γ (A' ∷ Γ₁) Λ Δ eq
  cong-Ic [] .(Γ₀ ++ Δ) (⊗ruf {.Γ₀} {Δ} {A' = A'}) refl | inj₁ (Γ₀ , refl , refl) =
    ⊗ruf ∙ uf (⊗rIl ∙ Il ⊗ruf)
  cong-Ic (x ∷ Γ) .(Γ₀ ++ Δ) {A = A} (⊗ruf {.(Γ ++ A ∷ Γ₀)} {Δ} {A' = .x}) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀ Δ A = ⊗ruf
  cong-Ic .(A' ∷ Γ₁ ++ Γ₀) Λ {A = A} (⊗ruf {Γ₁} {.(Γ₀ ++ A ∷ Λ)} {A' = A'}) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ₁ Λ A = ⊗ruf
  cong-Ic Γ Λ (⊗rIl {Γ₁} {Δ}) eq with  cases++ Γ Γ₁ Λ Δ eq
  cong-Ic Γ .(Γ₀ ++ Δ) (⊗rIl {.(Γ ++ _ ∷ Γ₀)} {Δ}) eq | inj₁ (Γ₀ , refl , refl) = ⊗rIl
  cong-Ic .(Γ₁ ++ Γ₀) Λ (⊗rIl {Γ₁} {.(Γ₀ ++ _ ∷ Λ)}) eq | inj₂ (Γ₀ , refl , refl) = ⊗rIl
  cong-Ic Γ Λ (⊗r⊗l {Γ₁} {Δ}) eq with cases++ Γ Γ₁ Λ Δ eq
  cong-Ic Γ .(Γ₀ ++ Δ) {A = A} (⊗r⊗l {.(Γ ++ A ∷ Γ₀)} {Δ}) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀ Δ A = ⊗r⊗l
  cong-Ic .(Γ₁ ++ Γ₀) Λ {A = A} (⊗r⊗l {Γ₁} {.(Γ₀ ++ A ∷ Λ)}) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ₁ Λ A = ⊗r⊗l
  cong-Ic Γ Λ (⊗c Γ₁ Δ {J = J} {J'} p) eq with cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Δ) eq
  cong-Ic Γ .(Γ₀ ++ J ⊗ J' ∷ Δ) (⊗c .(Γ ++ _ ∷ Γ₀) Δ {J = J} {J'} p) eq | inj₁ (Γ₀ , refl , refl) =
    ⊗c (Γ ++ I ∷ _ ∷ Γ₀) Δ (cong-Ic Γ (Γ₀ ++ _ ∷ _ ∷ Δ) p refl)
  cong-Ic .Γ₁ .Δ (⊗c Γ₁ Δ {J = J} {J'} p) eq | inj₂ ([] , refl , refl) =
    ⊗c (Γ₁ ++ I ∷ []) Δ (cong-Ic Γ₁ (_ ∷ Δ) p refl)
  cong-Ic .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ (⊗c Γ₁ .(Γ₀ ++ _ ∷ Λ) {J = J} {J'} p) eq | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) =
    ⊗c Γ₁ (Γ₀ ++ I ∷ _ ∷ Λ) (cong-Ic (Γ₁ ++ J ∷ J' ∷ Γ₀) Λ p refl)
  cong-Ic Γ Λ (uf⊗c1 {Γ₁} {J = J} {J'}) eq with cases++ Γ [] Λ (J ⊗ J' ∷ Γ₁) eq
  ... | inj₁ (Γ₀ , r , q) = ⊥-elim (⊥-elim ([]disj∷ Γ r))
  cong-Ic [] Λ (uf⊗c1 {.Λ} {J = J} {J'}) refl | inj₂ (.[] , refl , refl) =
    uf (Il uf⊗c1 ∙ Il⊗c) ∙ uf⊗c2
  cong-Ic (.(J ⊗ J') ∷ Γ) Λ (uf⊗c1 {.(Γ ++ _ ∷ Λ)} {J = J} {J'}) refl | inj₂ (.(J ⊗ J' ∷ Γ) , refl , refl) =
    uf⊗c1
  cong-Ic Γ Λ (⊗c⊗c {Γ = Γ₁} {Δ} {Λ₁} {J = J} {J'} {K} {K'}) eq with  cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Δ ++ K ⊗ K' ∷ Λ₁) eq
  cong-Ic Γ .(Γ₀ ++ J ⊗ J' ∷ Δ ++ K ⊗ K' ∷ Λ₁) {A = A} (⊗c⊗c {Γ = .(Γ ++ A ∷ Γ₀)} {Δ} {Λ₁} {J = J} {J'} {K} {K'}) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ (Γ₀ ++ J ∷ J' ∷ Δ) (K ⊗ K' ∷ Λ₁) A | cases++-inj₁ Γ (Γ₀ ++ J ⊗ J' ∷ Δ) (K ⊗ K' ∷ Λ₁) A | cases++-inj₁ Γ Γ₀ (J ⊗ J' ∷ Δ ++ K ∷ K' ∷ Λ₁) A =
    ⊗c⊗c {Γ = Γ ++ I ∷ A ∷ Γ₀}
  cong-Ic Γ .(Δ ++ K ⊗ K' ∷ Λ₁) (⊗c⊗c {Γ = _} {Δ} {Λ₁} {J = J} {J'} {K} {K'}) refl | inj₂ ([] , refl , refl) 
    rewrite cases++-inj₁ Γ (J' ∷ Δ) (K ⊗ K' ∷ Λ₁) J | cases++-inj₁ Γ Δ (K ⊗ K' ∷ Λ₁) (J ⊗ J') | cases++-inj₂ [] Γ (Δ ++ K ∷ K' ∷ Λ₁) (J ⊗ J')  =
      ⊗c⊗c {Γ = Γ ++ I ∷ []}
  cong-Ic .(Γ₁ ++ x ∷ Γ₀) Λ (⊗c⊗c {Γ = Γ₁} {Δ} {Λ₁} {J = J} {J'} {K} {K'}) eq | inj₂ (x ∷ Γ₀ , r , refl) with inj∷ r
  cong-Ic .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ (⊗c⊗c {Γ = Γ₁} {Δ} {Λ₁} {J = J} {J'} {K} {K'}) eq | inj₂ (.(J ⊗ J') ∷ Γ₀ , r , refl) | refl , q with cases++ Γ₀ Δ Λ (K ⊗ K' ∷ Λ₁) q
  cong-Ic ._ .(Γ₀' ++ K ⊗ K' ∷ Λ₁) {A = A} (⊗c⊗c {Γ = Γ₁} {.(Γ₀ ++ A ∷ Γ₀')} {Λ₁} {J = J} {J'} {K} {K'}) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | refl , refl | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ (Γ₁ ++ J ∷ J' ∷ Γ₀) Γ₀' (K ⊗ K' ∷ Λ₁) A | cases++-inj₁ (Γ₁ ++ J ⊗ J' ∷ Γ₀) Γ₀' (K ⊗ K' ∷ Λ₁) A | cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ₁ (Γ₀' ++ K ∷ K' ∷ Λ₁) A =
    ⊗c⊗c {Γ = Γ₁}{Γ₀ ++ I ∷ A ∷ Γ₀'}
  cong-Ic .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ (⊗c⊗c {Γ = Γ₁} {_} {.Λ} {J = J} {J'} {K} {K'}) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) | refl , refl | inj₂ ([] , refl , refl) 
    rewrite cases++-inj₂ [] (Γ₁ ++ J ∷ J' ∷ Γ₀) Λ (K ⊗ K') | cases++-inj₂ [] (Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ (K ⊗ K') | cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ₁ (K' ∷ Λ) K =
      ⊗c⊗c {Γ = Γ₁}{Γ₀ ++ I ∷ []}
  cong-Ic ._ Λ {A = A} (⊗c⊗c {Γ = Γ₁} {Δ} {.(Γ₀' ++ A ∷ Λ)} {J = J} {J'} {K} {K'}) refl | inj₂ (.(J ⊗ J') ∷ _ , refl , refl) | refl , refl | inj₂ (.(K ⊗ K') ∷ Γ₀' , refl , refl)
    rewrite cases++-inj₂ (K ⊗ K' ∷ Γ₀') (Γ₁ ++ J ∷ J' ∷ Δ) Λ A | cases++-inj₂ (K ⊗ K' ∷ Γ₀') (Γ₁ ++ J ⊗ J' ∷ Δ) Λ A | cases++-inj₂ (J ⊗ J' ∷ Δ ++ K ∷ K' ∷ Γ₀') Γ₁ Λ A = ⊗c⊗c
  cong-Ic Γ Λ (uf⊗c2 {Γ₁} {Δ} {A} {J = J} {J'}) eq with cases++ Γ (A ∷ Γ₁) Λ (J ⊗ J' ∷ Δ) eq
  cong-Ic [] .(Γ₀ ++ J ⊗ J' ∷ Δ) (uf⊗c2 {.Γ₀} {Δ} {A} {J = J} {J'}) refl | inj₁ (Γ₀ , refl , refl) =
    uf (Il uf⊗c2 ∙ Il⊗c) ∙ uf⊗c2
  cong-Ic (x ∷ Γ) .(Γ₀ ++ J ⊗ J' ∷ Δ) {A = A} (uf⊗c2 {.(Γ ++ A ∷ Γ₀)} {Δ} {.x} {J = J} {J'}) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀ (J ⊗ J' ∷ Δ) A = uf⊗c2 {Γ = Γ ++ I ∷ A ∷ Γ₀}
  cong-Ic .(A ∷ Γ₁) Λ (uf⊗c2 {Γ₁} {.Λ} {A} {J = J} {J'}) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ₁ Λ (J ⊗ J') = uf⊗c2 {Γ = Γ₁ ++ I ∷ []}
  cong-Ic .(A ∷ Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ {A = A₁} (uf⊗c2 {Γ₁} {.(Γ₀ ++ A₁ ∷ Λ)} {A} {J = J} {J'}) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) 
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ₁ Λ A₁ = uf⊗c2
  cong-Ic Γ Λ (Il⊗c {Γ₁} {Δ} {J = J} {J'}) eq with cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Δ) eq
  cong-Ic Γ .(Γ₀ ++ J ⊗ J' ∷ Δ) (Il⊗c {.(Γ ++ _ ∷ Γ₀)} {Δ} {J = J} {J'}) eq | inj₁ (Γ₀ , refl , refl) = Il⊗c {Γ  = Γ ++ I ∷ _ ∷ Γ₀}
  cong-Ic Γ Λ (Il⊗c {_} {.Λ} {J = J} {J'}) refl | inj₂ ([] , refl , refl) = Il⊗c {Γ = Γ ++ I ∷ []}
  cong-Ic .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ (Il⊗c {Γ₁} {.(Γ₀ ++ _ ∷ Λ)} {J = J} {J'}) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) = Il⊗c
  cong-Ic Γ Λ (⊗l⊗c {Γ₁} {Δ} {J = J} {J'}) eq with cases++ Γ Γ₁ Λ (J ⊗ J' ∷ Δ) eq
  cong-Ic Γ .(Γ₀ ++ J ⊗ J' ∷ Δ) {A = A} (⊗l⊗c {.(Γ ++ A ∷ Γ₀)} {Δ} {J = J} {J'}) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀ (J ⊗ J' ∷ Δ) A = ⊗l⊗c {Γ = Γ ++ I ∷ A ∷ Γ₀}
  cong-Ic Γ Λ (⊗l⊗c {_} {.Λ} {J = J} {J'}) refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ Λ (J ⊗ J') = ⊗l⊗c {Γ = Γ ++ I ∷ []}
  cong-Ic .(Γ₁ ++ J ⊗ J' ∷ Γ₀) Λ {A = A} (⊗l⊗c {Γ₁} {.(Γ₀ ++ _ ∷ Λ)} {J = J} {J'}) refl | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ₁ Λ A = ⊗l⊗c
  cong-Ic Γ Λ (⊗r⊗c1 {Γ = Γ₁} {Γ'} {Δ} {J = J} {J'}) eq with cases++ Γ (Γ₁ ++ J ⊗ J' ∷ Γ') Λ Δ eq
  cong-Ic Γ .(Γ₀ ++ Δ) (⊗r⊗c1 {Γ = Γ₁} {Γ'} {Δ} {J = J} {J'}) eq | inj₁ (Γ₀ , r , refl) with cases++ Γ Γ₁ Γ₀ (J ⊗ J' ∷ Γ') r
  cong-Ic Γ .((Γ₀' ++ J ⊗ J' ∷ Γ') ++ Δ) {A = A} (⊗r⊗c1 {Γ = .(Γ ++ _ ∷ Γ₀')} {Γ'} {Δ} {J = J} {J'}) refl | inj₁ (.(Γ₀' ++ J ⊗ J' ∷ Γ') , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ Γ Γ₀' (J ⊗ J' ∷ Γ')  A | cases++-inj₁  Γ Γ₀' (J ⊗ J' ∷ Γ' ++ Δ)  A | cases++-inj₁ Γ (Γ₀' ++ J ∷ J' ∷ Γ') Δ A = ⊗r⊗c1 {Γ = Γ ++ I ∷ A ∷ Γ₀'}
  cong-Ic Γ .(Γ₀ ++ Δ) (⊗r⊗c1 {Γ = _} {.Γ₀} {Δ} {J = J} {J'}) refl | inj₁ (Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ Γ₀ (J ⊗ J') | cases++-inj₂ [] Γ (Γ₀ ++ Δ) (J ⊗ J') | cases++-inj₁ Γ (J' ∷ Γ₀) Δ J = ⊗r⊗c1 {Γ = Γ ++ I ∷ []}
  cong-Ic .(Γ₁ ++ J ⊗ J' ∷ Γ₀') .(Γ₀ ++ Δ) {A = A} (⊗r⊗c1 {Γ = Γ₁} {.(Γ₀' ++ A ∷ Γ₀)} {Δ} {J = J} {J'}) refl | inj₁ (Γ₀ , refl , refl) | inj₂ (.(J ⊗ J') ∷ Γ₀' , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ₁ Γ₀ A | cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ₁ (Γ₀ ++ Δ) A | cases++-inj₁ (Γ₁ ++ J ∷ J' ∷ Γ₀') Γ₀ Δ A =  ⊗r⊗c1
  cong-Ic .(Γ₁ ++ J ⊗ J' ∷ Γ' ++ Γ₀) Λ {A = A} (⊗r⊗c1 {Γ = Γ₁} {Γ'} {.(Γ₀ ++ _ ∷ Λ)} {J = J} {J'}) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ' ++ Γ₀) Γ₁ Λ A | cases++-inj₂ Γ₀ (Γ₁ ++ J ∷ J' ∷ Γ') Λ A = ⊗r⊗c1
  cong-Ic Γ Λ (⊗r⊗c2 {Γ = Γ₁} {Δ} {Δ'} {J = J} {J'}) eq with cases++ Γ Γ₁ Λ (Δ ++ J ⊗ J' ∷ Δ') eq
  cong-Ic Γ .(Γ₀ ++ Δ ++ J ⊗ J' ∷ Δ') {A = A} (⊗r⊗c2 {Γ = .(Γ ++ A ∷ Γ₀)} {Δ} {Δ'} {J = J} {J'}) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Γ (Γ₀ ++ Δ) (J ⊗ J' ∷ Δ') A | cases++-inj₁ Γ Γ₀ (Δ ++ J ∷ J' ∷ Δ') A = ⊗r⊗c2
  cong-Ic .(Γ₁ ++ Γ₀) Λ (⊗r⊗c2 {Γ = Γ₁} {Δ} {Δ'} {J = J} {J'}) eq | inj₂ (Γ₀ , r , refl) with cases++ Γ₀ Δ Λ (J ⊗ J' ∷ Δ') r
  cong-Ic .(Γ₁ ++ Γ₀) .(Γ₀' ++ J ⊗ J' ∷ Δ') {A = A} (⊗r⊗c2 {Γ = Γ₁} {.(Γ₀ ++ A ∷ Γ₀')} {Δ'} {J = J} {J'}) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
    rewrite cases++-inj₁ Γ₀ Γ₀' (J ⊗ J' ∷ Δ') A | cases++-inj₁ (Γ₁ ++ Γ₀) Γ₀' (J ⊗ J' ∷ Δ') A | cases++-inj₂ Γ₀ Γ₁  (Γ₀' ++ J ∷ J' ∷ Δ') A = ⊗r⊗c2 {Γ = _}{Γ₀ ++ I ∷ A ∷ Γ₀'}
  cong-Ic .(Γ₁ ++ Γ₀) Λ (⊗r⊗c2 {Γ = Γ₁} {_} {.Λ} {J = J} {J'}) refl | inj₂ (Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ₀ Λ (J ⊗ J') | cases++-inj₂ [] (Γ₁ ++ Γ₀) Λ (J ⊗ J') | cases++-inj₂ Γ₀ Γ₁ (J' ∷ Λ) J = ⊗r⊗c2 {Γ = _}{Γ₀ ++ I ∷ []}
  cong-Ic .(Γ₁ ++ Δ ++ J ⊗ J' ∷ Γ₀') Λ {A = A} (⊗r⊗c2 {Γ = Γ₁} {Δ} {.(Γ₀' ++ _ ∷ Λ)} {J = J} {J'}) refl | inj₂ (.(Δ ++ J ⊗ J' ∷ Γ₀') , refl , refl) | inj₂ (.(J ⊗ J') ∷ Γ₀' , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') Δ Λ A | cases++-inj₂ (J ⊗ J' ∷ Γ₀') (Γ₁ ++ Δ) Λ A | cases++-inj₂ (Δ ++ J ∷ J' ∷ Γ₀') Γ₁ Λ A = ⊗r⊗c2

-- More laws

  mutual
    let⊗-[] : {Γ : Cxt} (Δ : Cxt) → {C J J' : Fma}
      → (f : nothing ∣ Γ ⊢ J ⊗ J')(g : just J ∣ J' ∷ Δ ⊢ C)
      → let⊗ false [] Δ f (uf g) ≗ scut f (⊗l g)
    let⊗-[] Δ₀ (uf f) g = let⊗-[]-j Δ₀ f g
    let⊗-[] Δ₀ (⊗r f f₁) g = refl
    let⊗-[] Δ₀ (⊗c Γ Δ f) g = ⊗c Γ (Δ ++ Δ₀) (let⊗-[] Δ₀ f g )

    let⊗-[]-true : {Γ : Cxt} (Δ : Cxt) → {C J J' : Fma}
      → (f : nothing ∣ Γ ⊢ J ⊗ J')(g : just J ∣ J' ∷ Δ ⊢ C)
      → let⊗ true [] Δ f (uf g) ≗ uf (Il (scut f (⊗l g)))
    let⊗-[]-true Δ₀ (uf {Γ} f) g = cong-Ic [] (Γ ++ Δ₀) (let⊗-[]-j Δ₀ f g) refl 
    let⊗-[]-true Δ₀ (⊗r f f₁) g = refl
    let⊗-[]-true Δ₀ (⊗c Γ Δ f) g =
      ⊗c (I ∷ Γ) (Δ ++ Δ₀) (let⊗-[]-true Δ₀ f g)
      ∙ ~ uf⊗c2
      ∙ uf (~ Il⊗c)

    let⊗-[]-j : {b : Bool}{Γ : Cxt} (Δ : Cxt) → {A C J J' : Fma}
      → (f : just A ∣ Γ ⊢ J ⊗ J')(g : just J ∣ J' ∷ Δ ⊢ C)
      → let⊗ b [] Δ f (uf g) ≗ uf (scut f (⊗l g))
    let⊗-[]-j Δ ax g = ~ uf⊗c1
    let⊗-[]-j Δ (⊗r f f₁) g = refl
    let⊗-[]-j Δ (Il f) g = let⊗-[]-true Δ f g
    let⊗-[]-j Δ (⊗l  {Γ = Γ} f) g = ⊗c [] (Γ ++ Δ) (let⊗-[]-j Δ f g) ∙ (~ uf⊗c1)
    let⊗-[]-j Δ (⊗c Γ Δ₁ f) g = ⊗c (_ ∷ Γ) (Δ₁ ++ Δ) (let⊗-[]-j Δ f g) ∙ (~ uf⊗c2)


  ccut-Il : (b : Bool) {S : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             (f : nothing ∣ Γ ⊢ A)(g : S ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ') → 
            ccut b Δ₀ (Il f) g eq ≡ ccut true Δ₀ f g eq
  ccut-Il b Δ₀ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq) 
  ccut-Il b Δ₀ f (uf g) eq with cases∷ Δ₀ eq
  ccut-Il b .[] f (uf g) eq | inj₁ (refl , refl , refl) = refl
  ccut-Il b .(_ ∷ Γ₀) f (uf g) eq | inj₂ (Γ₀ , refl , refl) = cong uf (ccut-Il b Γ₀ f g refl)
  ccut-Il b Δ₀ f Ir eq = ⊥-elim ([]disj∷ Δ₀ eq) 
  ccut-Il b Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
  ccut-Il b Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) eq | inj₁ (Γ₀ , refl , refl) =
    cong (λ x → ⊗r {Γ = Δ₀ ++ _ ∷ _ ++ Γ₀} x g₁) (ccut-Il b Δ₀ f g refl)
  ccut-Il b .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) eq | inj₂ (Γ₀ , refl , refl) =
    cong (⊗r g) (ccut-Il b Γ₀ f g₁ refl)
  ccut-Il b Δ₀ f (Il g) eq = cong Il (ccut-Il b Δ₀ f g eq)
  ccut-Il b Δ₀ f (⊗l g) refl = cong ⊗l (ccut-Il b (_ ∷ Δ₀) f g refl)
  ccut-Il b Δ₀ {Δ'} f (⊗c Γ Δ {J} {J'} g) eq with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) eq
  ccut-Il b {Γ = Γ} Δ₀ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ {J} {J'} g) eq | inj₁ (Γ₀ , refl , refl) =
    cong (⊗c (Δ₀ ++ I ∷ Γ ++ Γ₀) Δ) (ccut-Il b Δ₀ f g refl)
  ccut-Il b .Γ {.Δ} f (⊗c Γ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl) = refl
  ccut-Il b .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') {J} {J'} g) eq | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) =
    cong (⊗c Γ (Γ₀ ++ I ∷ _ ++ Δ')) (ccut-Il b (Γ ++ _ ∷ _ ∷ Γ₀) f g refl)

  ccut-⊗l : (b : Bool) {S : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A A' B' C : Fma} → 
             (f : just A' ∣ B' ∷ Γ ⊢ A)(g : S ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ') → 
            ccut b Δ₀ (⊗l f) g eq ≗ ⊗c Δ₀ (Γ ++ Δ') (ccut b Δ₀ f g eq)
  ccut-⊗l b Δ₀ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq) 
  ccut-⊗l b Δ₀ f (uf g) eq with cases∷ Δ₀ eq
  ccut-⊗l b .[] f (uf g) eq | inj₁ (refl , refl , refl) = uf⊗c1
  ccut-⊗l b .(_ ∷ Γ₀) f (uf g) eq | inj₂ (Γ₀ , refl , refl) = uf (ccut-⊗l b Γ₀ f g refl) ∙ uf⊗c2
  ccut-⊗l b Δ₀ f Ir eq = ⊥-elim ([]disj∷ Δ₀ eq) 
  ccut-⊗l b Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
  ccut-⊗l b Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) eq | inj₁ (Γ₀ , refl , refl) =
    ⊗r (ccut-⊗l b Δ₀ f g refl) refl ∙ ⊗r⊗c1
  ccut-⊗l b .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) eq | inj₂ (Γ₀ , refl , refl) =
    ⊗r refl (ccut-⊗l b Γ₀ f g₁ refl) ∙ ⊗r⊗c2
  ccut-⊗l b Δ₀ f (Il g) eq = Il (ccut-⊗l b Δ₀ f g eq) ∙ Il⊗c
  ccut-⊗l b Δ₀ f (⊗l g) refl = ⊗l (ccut-⊗l b (_ ∷ Δ₀) f g refl) ∙ ⊗l⊗c
  ccut-⊗l b Δ₀ {Δ'} f (⊗c Γ Δ {J} {J'} g) eq with cases++ Δ₀ Γ Δ' (J ⊗ J' ∷ Δ) eq
  ccut-⊗l b {Γ = Γ} Δ₀ {.(Γ₀ ++ J ⊗ J' ∷ Δ)} f (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ {J} {J'} g) eq | inj₁ (Γ₀ , refl , refl) =
    ⊗c (Δ₀ ++ _ ∷ Γ ++ Γ₀) Δ (ccut-⊗l b Δ₀ f g refl) ∙ ~ ⊗c⊗c {Γ = Δ₀}{Γ ++ Γ₀}{Δ} 
  ccut-⊗l b .Γ {.Δ} f (⊗c Γ Δ {J} {J'} g) refl | inj₂ ([] , refl , refl) = refl
  ccut-⊗l b .(Γ ++ J ⊗ J' ∷ Γ₀) {Δ'} f (⊗c Γ .(Γ₀ ++ _ ∷ Δ') {J} {J'} g) eq | inj₂ (.(J ⊗ J') ∷ Γ₀ , refl , refl) =
    ⊗c Γ (Γ₀ ++ _ ∷ _ ++ Δ') (ccut-⊗l b (Γ ++ _ ∷ _ ∷ Γ₀) f g refl) ∙ ⊗c⊗c


  
  
  
  let⊗-uf : {b : Bool}{S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {A C J J' : Fma}
               (f : S ∣ Γ ⊢ J ⊗ J')(g : just A ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)  →
              let⊗ b (A ∷ Δ₁) Δ₂ f (uf g) ≗ uf (let⊗ b Δ₁ Δ₂ f g)
  let⊗-uf Δ₁ Δ₂ ax g = ~ uf⊗c2
  let⊗-uf {false} Δ₁ Δ₂ (uf f) g = let⊗-uf Δ₁ Δ₂ f g
  let⊗-uf {true} Δ₁ Δ₂ (uf f) g =
    cong-Ic (_ ∷ Δ₁) (_ ++ Δ₂) (let⊗-uf Δ₁ Δ₂ f g) refl
  let⊗-uf Δ₁ Δ₂ (⊗r f f₁) g = refl
  let⊗-uf {Γ = Γ} Δ₁ Δ₂ (Il f) g = let⊗-uf Δ₁ Δ₂ f g
  let⊗-uf {Γ = Γ} Δ₁ Δ₂ (⊗l f) g = ⊗c (_ ∷ Δ₁) (Γ ++ Δ₂) (let⊗-uf Δ₁ Δ₂ f g) ∙ (~ uf⊗c2)
  let⊗-uf {b}{S} Δ₁ Δ₂ (⊗c Γ Δ f) g = ⊗c (_ ∷ Δ₁ ++ asCxt b S Γ) (Δ ++ Δ₂) (let⊗-uf Δ₁ Δ₂ f g) ∙ (~ uf⊗c2 {Γ = Δ₁ ++ asCxt b S Γ} )
  
  let⊗-Il : {b : Bool} {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {C J J' : Fma} → 
               (f : S ∣ Γ ⊢ J ⊗ J')(g : nothing ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)  →
              let⊗ b Δ₁ Δ₂ f (Il g) ≗ Il (let⊗ b Δ₁ Δ₂ f g)
  let⊗-Il Δ₁ Δ₂ ax g = ~ Il⊗c
  let⊗-Il {false} Δ₁ Δ₂ (uf f) g = let⊗-Il Δ₁ Δ₂ f g
  let⊗-Il {true} Δ₁ Δ₂ (uf f) g = cong-Ic Δ₁ (_ ++ Δ₂) (let⊗-Il Δ₁ Δ₂ f g) refl
  let⊗-Il Δ₁ Δ₂ (⊗r f f₁) g = refl
  let⊗-Il {Γ = Γ} Δ₁ Δ₂ (Il f) g = let⊗-Il Δ₁ Δ₂ f g
  let⊗-Il {Γ = Γ} Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₁ (Γ ++ Δ₂) (let⊗-Il Δ₁ Δ₂ f g) ∙ ~ Il⊗c
  let⊗-Il {b}{S} Δ₁ Δ₂ (⊗c Γ Δ f) g = ⊗c (Δ₁ ++ asCxt b S Γ) (Δ ++ Δ₂) (let⊗-Il Δ₁ Δ₂ f g) ∙ ~ Il⊗c {Γ = Δ₁ ++ asCxt b S Γ}
  
  let⊗-⊗l : {b : Bool} {S : Stp} → {Γ : Cxt} (Δ₁ Δ₂ : Cxt) → {A B C J J' : Fma} → 
               (f : S ∣ Γ ⊢ J ⊗ J')(g : just A ∣ B ∷ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)  →
              let⊗ b Δ₁ Δ₂ f (⊗l g) ≗ ⊗l (let⊗ b (B ∷ Δ₁) Δ₂ f g)
  let⊗-⊗l Δ₁ Δ₂ ax g = ~ ⊗l⊗c
  let⊗-⊗l {false} Δ₁ Δ₂ (uf f) g = let⊗-⊗l Δ₁ Δ₂ f g
  let⊗-⊗l {true} Δ₁ Δ₂ (uf f) g = cong-Ic Δ₁ (_ ++ Δ₂) (let⊗-⊗l Δ₁ Δ₂ f g) refl 
  let⊗-⊗l Δ₁ Δ₂ (⊗r f f₁) g = refl
  let⊗-⊗l {Γ = Γ} Δ₁ Δ₂ (Il f) g = let⊗-⊗l Δ₁ Δ₂ f g
  let⊗-⊗l {Γ = Γ} Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₁ (Γ ++ Δ₂) (let⊗-⊗l Δ₁ Δ₂ f g) ∙ ~ ⊗l⊗c
  let⊗-⊗l {b} {S} Δ₁ Δ₂ (⊗c Γ Δ f) g = ⊗c (Δ₁ ++ asCxt b S Γ) (Δ ++ Δ₂) (let⊗-⊗l Δ₁ Δ₂ f g) ∙ ~ ⊗l⊗c {Γ = Δ₁ ++ asCxt b S Γ}
  
  let⊗-⊗r1 : {b : Bool} {S T : Stp} → {Γ Δ : Cxt} (Δ₁ Δ₂ : Cxt) → {A B J J' : Fma} → 
               (f : S ∣ Γ ⊢ J ⊗ J')(g : T ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ A)(g' : nothing ∣ Δ ⊢ B)  →
              let⊗ b Δ₁ (Δ₂ ++ Δ) f (⊗r g g') ≗ ⊗r (let⊗ b Δ₁ Δ₂ f g) g'
  let⊗-⊗r1 Δ₁ Δ₂ ax g g' = ~ ⊗r⊗c1
  let⊗-⊗r1 {false} Δ₁ Δ₂ (uf f) g g' = let⊗-⊗r1 Δ₁ Δ₂ f g g'
  let⊗-⊗r1 {true} {Δ = Δ} Δ₁ Δ₂ (uf {Γ}{A} f) g g' with cong-Ic Δ₁ (Γ ++ Δ₂ ++ Δ) (let⊗-⊗r1 {true} Δ₁ Δ₂ f g g') refl
  ... | ih rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₂) Δ A = ih 
  let⊗-⊗r1 {Δ = Δ} Δ₁ Δ₂ {J = J} {J'} (⊗r {Δ = Δ₃} f f₁) g g'
    rewrite cases++-inj₁ (Δ₁ ++ J ∷ []) Δ₂ Δ J' | cases++-inj₁ Δ₁ (Δ₃ ++ Δ₂) Δ J = refl
  let⊗-⊗r1 {Γ = Γ}{Δ} Δ₁ Δ₂ (Il f) g g' = let⊗-⊗r1 Δ₁ Δ₂ f g g' 
  let⊗-⊗r1 {Γ = Γ}{Δ} Δ₁ Δ₂ (⊗l f) g g' = ⊗c Δ₁ (Γ ++ Δ₂ ++ Δ) (let⊗-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c1)
  let⊗-⊗r1 {b}{S} {Δ = Δ₃} Δ₁ Δ₂ (⊗c Γ Δ f) g g' = ⊗c (Δ₁ ++ asCxt b S Γ) (Δ ++ Δ₂ ++ Δ₃) (let⊗-⊗r1 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c1 {Γ = Δ₁ ++ asCxt b S Γ})


  let⊗-⊗r2 : {b : Bool} {S T : Stp} → {Γ Δ : Cxt} (Δ₁ Δ₂ : Cxt) → {A B J J' : Fma} → 
               (f : S ∣ Γ ⊢ J ⊗ J')(g : T ∣ Δ ⊢ A)(g' : nothing ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ B)  →
              let⊗ b (Δ ++ Δ₁) Δ₂ f (⊗r g g') ≗ ⊗r g (let⊗ b Δ₁ Δ₂ f g')
  let⊗-⊗r2 Δ₁ Δ₂ ax g g' =  ~ ⊗r⊗c2
  let⊗-⊗r2 {false} Δ₁ Δ₂ (uf f) g g' = let⊗-⊗r2 Δ₁ Δ₂ f g g'
  let⊗-⊗r2 {true} {Δ = Δ} Δ₁ Δ₂ (uf {Γ} {A} f) g g' with cong-Ic (Δ ++ Δ₁) (Γ ++ Δ₂) (let⊗-⊗r2 {true} Δ₁ Δ₂ f g g') refl
  ... | ih rewrite cases++-inj₂ Δ₁ Δ (Γ ++ Δ₂) A = ih 
  let⊗-⊗r2 {Δ = Δ} Δ₁ Δ₂ {J = J} {J'} (⊗r {Δ = Δ₃} f f₁) g g'
    rewrite cases++-inj₂ (Δ₁ ++ J ∷ []) Δ Δ₂ J' | cases++-inj₂ Δ₁ Δ (Δ₃ ++ Δ₂) J = refl
  let⊗-⊗r2 {Γ = Γ}{Δ} Δ₁ Δ₂ (Il f) g g' = let⊗-⊗r2 Δ₁ Δ₂ f g g'
  let⊗-⊗r2 {Γ = Γ}{Δ} Δ₁ Δ₂ (⊗l f) g g' = ⊗c (Δ ++ Δ₁) (Γ ++ Δ₂) (let⊗-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c2)
  let⊗-⊗r2 {b}{S} {Δ = Δ₃} Δ₁ Δ₂ (⊗c Γ Δ f) g g' = ⊗c (Δ₃ ++ Δ₁ ++ asCxt b S Γ) (Δ ++ Δ₂) (let⊗-⊗r2 Δ₁ Δ₂ f g g') ∙ (~ ⊗r⊗c2 {Γ = Δ₃}{Δ₁ ++ asCxt b S Γ})
  
  let⊗-⊗c1 : {b : Bool} {S T : Stp} → {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) → {C J J' K K' : Fma} →
               (f : S ∣ Γ ⊢ K ⊗ K')(g : T ∣ Δ₀ ++ K ∷ K' ∷ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ C)  →
              let⊗ b Δ₀ (Δ₁ ++ J ⊗ J' ∷ Δ₂) f (⊗c (Δ₀ ++ K ∷ K' ∷ Δ₁) Δ₂ g)
                ≗ ⊗c (Δ₀ ++ asCxt b S Γ ++ Δ₁) Δ₂ (let⊗ b Δ₀ (Δ₁ ++ J ∷ J' ∷ Δ₂) f g)
  let⊗-⊗c1 Δ₀ Δ₁ Δ₂ ax g = ⊗c⊗c
  let⊗-⊗c1 {false} Δ₀ Δ₁ Δ₂ (uf f) g = let⊗-⊗c1 Δ₀ Δ₁ Δ₂ f g
  let⊗-⊗c1 {true} Δ₀ Δ₁ Δ₂ {J = J} {J'} (uf {Γ} {A} f) g with cong-Ic Δ₀ (Γ ++ Δ₁ ++ J ⊗ J' ∷ Δ₂) (let⊗-⊗c1 {true} Δ₀ Δ₁ Δ₂ f g) refl
  ... | ih rewrite cases++-inj₁ Δ₀ (Γ ++ Δ₁) (J ⊗ J' ∷ Δ₂) A = ih 
  let⊗-⊗c1 Δ₀ Δ₁ Δ₂ {J = J} {J'} {K} {K'} (⊗r {Δ = Δ} f f₁) g 
    rewrite cases++-inj₁ (Δ₀ ++ K ∷ []) Δ₁ (J ⊗ J' ∷ Δ₂) K' | cases++-inj₁ Δ₀ (Δ ++ Δ₁) (J ⊗ J' ∷ Δ₂) K = refl
  let⊗-⊗c1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = let⊗-⊗c1 Δ₀ Δ₁ Δ₂ f g
  let⊗-⊗c1 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c Δ₀ (Γ ++ Δ₁ ++ _ ∷ Δ₂) (let⊗-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗c⊗c {Γ = Δ₀}{Γ ++ Δ₁}
  let⊗-⊗c1 {b}{S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ f) g = ⊗c (Δ₀ ++ asCxt b S Γ) (Δ ++ Δ₁ ++ _ ∷ Δ₂) (let⊗-⊗c1 Δ₀ Δ₁ Δ₂ f g) ∙ ⊗c⊗c {Γ = Δ₀ ++ asCxt b S Γ}{Δ ++ Δ₁}

  let⊗-⊗c2 : {b : Bool}{S T : Stp} → {Γ : Cxt} (Δ₀ Δ₁ Δ₂ : Cxt) →  {C J J' K K' : Fma} →
               (f : S ∣ Γ ⊢ K ⊗ K')(g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ₁ ++ K ∷ K' ∷ Δ₂ ⊢ C)  →
              let⊗ b (Δ₀ ++ J ⊗ J' ∷ Δ₁) Δ₂ f (⊗c Δ₀ (Δ₁ ++ K ∷ K' ∷ Δ₂) g)
                ≗ ⊗c Δ₀ (Δ₁ ++ asCxt b S Γ ++ Δ₂) (let⊗ b (Δ₀ ++ J ∷ J' ∷ Δ₁) Δ₂ f g)
  let⊗-⊗c2 Δ₀ Δ₁ Δ₂ ax g = ~ ⊗c⊗c
  let⊗-⊗c2 {false} Δ₀ Δ₁ Δ₂ (uf f) g = let⊗-⊗c2 Δ₀ Δ₁ Δ₂ f g
  let⊗-⊗c2 {true} Δ₀ Δ₁ Δ₂ {J = J} {J'} (uf {Γ} {A} f) g with cong-Ic (Δ₀ ++ J ⊗ J' ∷ Δ₁) (Γ ++ Δ₂) (let⊗-⊗c2 {true} Δ₀ Δ₁ Δ₂ f g) refl
  ... | ih rewrite cases++-inj₂ (J ⊗ J' ∷ Δ₁) Δ₀ (Γ ++ Δ₂) A = ih
  let⊗-⊗c2 Δ₀ Δ₁ Δ₂ {J = J} {J'} {K} {K'} (⊗r {Δ = Δ} f f₁) g
    rewrite cases++-inj₂ (J ⊗ J' ∷ Δ₁ ++ K ∷ []) Δ₀ Δ₂ K' | cases++-inj₂ (J ⊗ J' ∷ Δ₁) Δ₀ (Δ ++ Δ₂) K = refl
  let⊗-⊗c2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (Il f) g = let⊗-⊗c2 Δ₀ Δ₁ Δ₂ f g
  let⊗-⊗c2 {Γ = Γ} Δ₀ Δ₁ Δ₂ (⊗l f) g = ⊗c (Δ₀ ++ _ ∷ Δ₁) (Γ ++ Δ₂) (let⊗-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗c⊗c
  let⊗-⊗c2 {b}{S} Δ₀ Δ₁ Δ₂ (⊗c Γ Δ f) g = ⊗c (Δ₀ ++ _ ∷ Δ₁ ++ asCxt b S Γ) (Δ ++ Δ₂) (let⊗-⊗c2 Δ₀ Δ₁ Δ₂ f g) ∙ ~ ⊗c⊗c {Γ = Δ₀}{Δ₁ ++ asCxt b S Γ}

-- The rules scut, ccut and let⊗ are compatible with ≗

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
      scut f (ccut _ [] f' h refl)
      ≗〈 cong-scut1 p 〉
      scut g (ccut _ [] f' h refl)
      ≗〈 cong-scut2 g (cong-ccut1 [] h refl q) 〉
      scut g (ccut _ [] g' h refl)
      qed≗
    cong-scut⊗r {Γ = Γ₁} {Δ₁} (⊗c Γ Δ h) p q =
      ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ (cong-scut⊗r h p q)
  
  
  
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
    cong-scut1 {Δ' = Δ'} (⊗c Γ Δ p) = ⊗c Γ (Δ ++ Δ') (cong-scut1 p)
    cong-scut1 uf⊗c1 = uf⊗c1
    cong-scut1 ⊗c⊗c = ⊗c⊗c
    cong-scut1 uf⊗c2 = uf⊗c2
    cong-scut1 Il⊗c = Il⊗c
    cong-scut1 ⊗l⊗c = ⊗l⊗c
    cong-scut1 {h = ax} (⊗r⊗c1 {Γ = Γ} {Γ'} {f = f} {g}) = ⊗r⊗c1
    cong-scut1 {h = ⊗r {_}{Γ₁}{Δ₁} h h₁} (⊗r⊗c1 {Γ = Γ} {Γ'}  {Δ} {f = f} {g}) =
      ⊗r (cong-scut1 {f = ⊗r (⊗c Γ Γ' f) g}{⊗c Γ (Γ' ++ Δ) (⊗r f g)}{h} ⊗r⊗c1) refl
      ∙ ⊗r⊗c1
    cong-scut1 {h = ⊗l h} (⊗r⊗c1 {Γ = Γ} {Γ'} {f = f} {g}) = refl
    cong-scut1 {h = ⊗c Γ₁ Δ h} (⊗r⊗c1 {Γ = Γ} {Γ'} {Δ₁} {f = f} {g}) =
      ⊗c (Γ ++ _ ∷ Γ' ++ Δ₁ ++ Γ₁) Δ (cong-scut1 {f = ⊗r (⊗c Γ Γ' f) g}{⊗c Γ (Γ' ++ Δ₁) (⊗r f g)}{h} ⊗r⊗c1)
      ∙ (~ ⊗c⊗c {Γ = Γ}{Γ' ++ Δ₁ ++ Γ₁}{Δ}) 
    cong-scut1 {Δ' = .[]} {h = ax} (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) = ⊗r⊗c2
    cong-scut1 {Δ' = ._} {h = ⊗r {_}{Γ₁}{Δ₁} h h₁} (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) =
      ⊗r (cong-scut1 {f = ⊗r f (⊗c Δ Δ'' g)}{⊗c (Γ ++ Δ) Δ'' (⊗r f g)}{h} ⊗r⊗c2) refl
      ∙ ⊗r⊗c1 {Γ = Γ ++ Δ} {Δ'' ++ Γ₁} {Δ₁}
    cong-scut1 {Δ' = Δ'} {h = ⊗l h} (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) = 
      cong-scut2 f (ccut-⊗c [] Δ Δ'' g h refl) ∙ scut-⊗c Δ (Δ'' ++ Δ') f (ccut false [] g h refl)
    cong-scut1 {Δ' = .(Γ₁ ++ _ ⊗ _ ∷ Δ₁)} {h = ⊗c Γ₁ Δ₁ h} (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {f = f} {g}) =
      ⊗c (Γ ++ Δ ++ _ ∷ Δ'' ++ Γ₁) Δ₁ (cong-scut1 {f = ⊗r f (⊗c Δ Δ'' g)}{⊗c (Γ ++ Δ) Δ'' (⊗r f g)}{h} ⊗r⊗c2)
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
    cong-scut2 (⊗r {Γ = Γ} h h') (⊗r⊗l {f = f}{g}) = ~ (scut⊗r h (ccut _ [] h' f refl) g)
    cong-scut2 (⊗r {Γ = Γ₁} {Δ₁} h h') (⊗c Γ Δ p) = ⊗c (Γ₁ ++ Δ₁ ++ Γ) Δ (cong-scut2 (⊗r h h') p)
    cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (⊗c⊗c {Γ = Γ₁} {Δ₁} {Λ}) = ⊗c⊗c {Γ = Γ ++ Δ ++ Γ₁} {Δ₁} {Λ}
    cong-scut2 (⊗r {Δ = Δ} h h') (⊗l⊗c {Γ} {Δ₁} {f = f}) = scut-⊗c (Δ ++ Γ) Δ₁ h (ccut false [] h' f refl)
    cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (⊗r⊗c1 {Γ = Γ₁} {Γ'} {Δ₁}) = ⊗r⊗c1 {Γ = Γ ++ Δ ++ Γ₁} {Γ'} {Δ₁}
    cong-scut2 (⊗r h h') ⊗r⊗c2 = ⊗r⊗c2
    cong-scut2 (Il h) p = Il (cong-scut2 h p)
    cong-scut2 (⊗l h) p = ⊗l (cong-scut2 h p)
    cong-scut2 {Δ' = Δ'} (⊗c Γ Δ h) p = ⊗c Γ (Δ ++ Δ') (cong-scut2 h p)
  
    cong-ccut1 : {b : Bool} {S T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
               {f f' : S ∣ Γ ⊢ A}(g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
               f ≗ f' → ccut b Δ₀ f g r ≗ ccut b Δ₀ f' g r
    cong-ccut1 Δ₀ ax r p = ⊥-elim ([]disj∷ Δ₀ r)
    cong-ccut1 Δ₀ (uf g) r p with cases∷ Δ₀ r
    cong-ccut1 {false} {nothing} .[] (uf g) r p | inj₁ (refl , refl , refl) = cong-scut1 p
    cong-ccut1 {true} {nothing} .[] (uf g) r p | inj₁ (refl , refl , refl) = uf (Il (cong-scut1 p)) 
    cong-ccut1 {b}{just x} .[] (uf g) r p | inj₁ (refl , refl , refl) = uf (cong-scut1 p)  
    cong-ccut1 .(_ ∷ Δ₀) (uf g) r p | inj₂ (Δ₀ , refl , refl) = uf (cong-ccut1 Δ₀ g refl p)
    cong-ccut1 Δ₀ Ir r p = ⊥-elim ([]disj∷ Δ₀ r)
    cong-ccut1 Δ₀ {Δ'} (⊗r {Γ = Γ}{Δ} g g') r p with cases++ Δ₀ Γ Δ' Δ r
    cong-ccut1 Δ₀ (⊗r g g') r p | inj₁ (Γ₀ , refl , refl) = ⊗r (cong-ccut1 Δ₀ g refl p) refl
    cong-ccut1 ._ (⊗r g g') r p | inj₂ (Γ₀ , refl , refl) = ⊗r refl (cong-ccut1 Γ₀ g' refl p)
    cong-ccut1 Δ₀ (Il g) refl p = Il (cong-ccut1 Δ₀ g refl p)
    cong-ccut1 Δ₀ (⊗l {B = B} g) refl p = ⊗l (cong-ccut1 (B ∷ Δ₀) g refl p)
    cong-ccut1 Δ₀ {Δ'} (⊗c Γ Δ g) r p with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    cong-ccut1 {b}{S}{Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ g) refl p | inj₁ (Γ₀ , refl , refl) =
      ⊗c (Δ₀ ++ asCxt b S Γ ++ Γ₀) Δ (cong-ccut1 Δ₀ g refl p)
    cong-ccut1 .Γ {.Δ} (⊗c Γ Δ g) refl p | inj₂ ([] , refl , refl) = cong-let⊗1 Γ Δ g p 
    cong-ccut1 {b}{S}{Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} (⊗c Γ .(Γ₀ ++ _ ∷ Δ') g) refl p | inj₂ (_ ∷ Γ₀ , refl , refl) = 
      ⊗c Γ (Γ₀ ++ asCxt b S Γ₁ ++ Δ') (cong-ccut1 (Γ ++ _ ∷ _ ∷  Γ₀) g refl p)
  
    cong-let⊗1 : {b : Bool}{S T : Stp} {Γ : Cxt} → (Δ₀ Δ' : Cxt) → {C J J' : Fma} →
                 {f f' : S ∣ Γ ⊢ J ⊗ J'}(g : T ∣ Δ₀ ++ J ∷ J' ∷ Δ' ⊢ C)  → 
                 f ≗ f' → let⊗ b Δ₀ Δ' f g ≗ let⊗ b Δ₀ Δ' f' g
    cong-let⊗1 Δ₀ Δ' g refl = refl
    cong-let⊗1 Δ₀ Δ' g (~ p) = ~ cong-let⊗1 Δ₀ Δ' g p
    cong-let⊗1 Δ₀ Δ' g (p ∙ p₁) = cong-let⊗1 Δ₀ Δ' g p ∙ cong-let⊗1 Δ₀ Δ' g p₁
    cong-let⊗1 {false} Δ₀ Δ' g (uf p) = cong-let⊗1 Δ₀ Δ' g p
    cong-let⊗1 {true} Δ₀ Δ' g (uf p) = cong-Ic Δ₀ (_ ++ Δ') (cong-let⊗1 Δ₀ Δ' g p) refl 
    cong-let⊗1 {Γ = Γ} Δ₀ Δ' g (⊗l {g = g'} p) = ⊗c Δ₀ (Γ ++ Δ') (cong-let⊗1 Δ₀ Δ' g p)
    cong-let⊗1 {Γ = Γ} Δ₀ Δ' g (Il p) = cong-let⊗1 Δ₀ Δ' g p
    cong-let⊗1 Δ₀ Δ' g ax⊗ = 
      ⊗c Δ₀ Δ' (≡-to-≗ (sym (trans (ccut-ax Δ₀ (ccut false (Δ₀ ++ _ ∷ []) (uf ax) g refl) refl) (ccut-unit (Δ₀ ++ _ ∷ []) g refl)))) 
    cong-let⊗1 Δ₀ Δ' g (⊗r {g = g₁} {f'} p q) =
      cong-ccut1 Δ₀ (ccut false (Δ₀ ++ _ ∷ []) f' g refl) refl p
      ∙  cong-ccut2 Δ₀ {f = g₁} refl (cong-ccut1 (Δ₀ ++ _ ∷ []) g refl q) 
    cong-let⊗1 {false} Δ₀ Δ' g (⊗ruf {f = f} {g₁}) = ≡-to-≗ (ccut-uf Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) g₁ g refl) refl)
    cong-let⊗1 {true} Δ₀ Δ' g (⊗ruf {f = f} {g₁}) =
      ≡-to-≗ (ccut-uf-true Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) g₁ g refl) refl)
    cong-let⊗1 Δ₀ Δ' g (⊗rIl {Γ} {f = f} {g₁}) =
      ≡-to-≗ (ccut-Il _ Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) g₁ g refl) refl)
    cong-let⊗1 Δ₀ Δ' g (⊗r⊗l {Γ}{Δ} {f = f}{g₁}) = ccut-⊗l _ Δ₀ f (ccut false (Δ₀ ++ _ ∷ []) g₁ g refl) refl
    cong-let⊗1 Δ₀ Δ' g (⊗r⊗c1 {Γ = Γ} {Γ'} {f = f} {g₁}) = ccut-⊗c Δ₀ Γ Γ' f (ccut false (Δ₀ ++ _ ∷ []) g₁ g refl) refl
    cong-let⊗1 {b} Δ₀ Δ' {J = K} g (⊗r⊗c2 {Δ = Δ} {Δ''} {J = J}{J'} {f = f} {g₁}) with cong-ccut2 {b} Δ₀ {f = f} refl (ccut-⊗c {false} (Δ₀ ++ _ ∷ []) Δ Δ'' g₁ g refl)
    ... | ih rewrite cases++-inj₁ Δ₀ Δ (J ⊗ J' ∷ Δ'' ++ Δ') K = ih
    cong-let⊗1 {b}{S} Δ₀ Δ' g (⊗c Γ Δ p) = ⊗c (Δ₀ ++ asCxt b S Γ) (Δ ++ Δ') (cong-let⊗1 {b}{S} Δ₀ Δ' g p)
    cong-let⊗1 {false} Δ₀ Δ' g (uf⊗c1 {Γ} {f = f}) = refl
    cong-let⊗1 {true} Δ₀ Δ' g (uf⊗c1 {Γ} {J = J} {J'} {f})
      rewrite cases++-inj₂ [] Δ₀ (Γ ++ Δ') (J ⊗ J') = refl
    cong-let⊗1 {b}{S} Δ₀ Δ' g (⊗c⊗c {Γ = Γ} {Δ} {Λ}) = ⊗c⊗c {Γ = Δ₀ ++ asCxt b S Γ}{Δ}{Λ ++ Δ'}
    cong-let⊗1 {false} Δ₀ Δ' g uf⊗c2 = refl
    cong-let⊗1 {true} Δ₀ Δ' g (uf⊗c2 {Γ} {Δ} {A} {J = J} {J'})
      rewrite cases++-inj₁ Δ₀ Γ (J ⊗ J' ∷ Δ ++ Δ') A = refl
    cong-let⊗1 Δ₀ Δ' g Il⊗c = refl
    cong-let⊗1 Δ₀ Δ' g (⊗l⊗c {Γ} {Δ} {A} {B} {f = f}) = ⊗c⊗c {Γ = Δ₀}{Γ}{Δ ++ Δ'} 
  
    cong-let⊗2 : {b : Bool} {S T : Stp} {Γ : Cxt} → (Δ₀ Δ' : Cxt) → {C J J' : Fma} → 
                 (f : S ∣ Γ ⊢ J ⊗ J'){g g' : T ∣ Δ₀ ++ J ∷ J' ∷ Δ' ⊢ C}  → 
                 g ≗ g' → let⊗ b Δ₀ Δ' f g ≗ let⊗ b Δ₀ Δ' f g'
    cong-let⊗2 Δ₀ Δ' ax p = ⊗c Δ₀ Δ' p
    cong-let⊗2 {false} Δ₀ Δ' (uf f) p = cong-let⊗2 Δ₀ Δ' f p
    cong-let⊗2 {true} Δ₀ Δ' (uf f) p = cong-Ic Δ₀ (_ ++ Δ') (cong-let⊗2 Δ₀ Δ' f p) refl
    cong-let⊗2 Δ₀ Δ' (⊗r f f') p = cong-ccut2 Δ₀ {f = f} refl (cong-ccut2 (Δ₀ ++ _ ∷ []) {f = f'} refl p) 
    cong-let⊗2 Δ₀ Δ' (Il {Γ = Γ} f) p = cong-let⊗2 Δ₀ Δ' f p
    cong-let⊗2 Δ₀ Δ' (⊗l {Γ = Γ} f) p = ⊗c Δ₀ (Γ ++ Δ') (cong-let⊗2 Δ₀ Δ' f p)
    cong-let⊗2 {b}{S} Δ₀ Δ' (⊗c Γ Δ f) p = ⊗c (Δ₀ ++ asCxt b S Γ) (Δ ++ Δ') (cong-let⊗2 Δ₀ Δ' f p)
  
    
    cong-ccut2 : {b : Bool}{S T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
               {f : S ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C}  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
               g ≗ g' → ccut b Δ₀ f g r ≗ ccut b Δ₀ f g' r
    cong-ccut2 Δ₀ r refl = refl
    cong-ccut2 Δ₀ r (~ p) = ~ cong-ccut2 Δ₀ r p
    cong-ccut2 Δ₀ r (p ∙ p₁) = (cong-ccut2 Δ₀ r p) ∙ (cong-ccut2 Δ₀ r p₁)
    cong-ccut2 Δ₀ r (uf p) with cases∷ Δ₀ r
    cong-ccut2 {false} {nothing} .[] {f = f} r (uf p) | inj₁ (refl , refl , refl) = cong-scut2 f p 
    cong-ccut2 {true} {nothing} .[] {f = f} r (uf p) | inj₁ (refl , refl , refl) = uf (Il (cong-scut2 f p) ) 
    cong-ccut2 {_}{just x} .[] {f = f} r (uf p) | inj₁ (refl , refl , refl) = uf (cong-scut2 f p) 
    cong-ccut2 .(_ ∷ Γ₀) r (uf p) | inj₂ (Γ₀ , refl , refl) = uf (cong-ccut2 Γ₀ refl p)
    cong-ccut2 Δ₀ refl (⊗l {B = B} p) = ⊗l (cong-ccut2 (B ∷ Δ₀) refl p)
    cong-ccut2 Δ₀ refl (Il p) = Il (cong-ccut2 Δ₀ refl p)
    cong-ccut2 Δ₀ {Δ'} r (⊗r {Γ = Γ}{Δ} p p') with cases++ Δ₀ Γ Δ' Δ r
    cong-ccut2 Δ₀ r (⊗r p p') | inj₁ (Γ₀ , refl , refl) = ⊗r (cong-ccut2 Δ₀ refl p) p'
    cong-ccut2 ._ r (⊗r p p') | inj₂ (Γ₀ , refl , refl) = ⊗r p (cong-ccut2 Γ₀ refl p')
    cong-ccut2 Δ₀ r axI = ⊥-elim ([]disj∷ Δ₀ r)
    cong-ccut2 Δ₀ r ax⊗ = ⊥-elim ([]disj∷ Δ₀ r)
    cong-ccut2 Δ₀ {Δ'} r (⊗ruf {Γ} {Δ}) with cases++ Δ₀ (_ ∷ Γ) Δ' Δ r
    cong-ccut2 {false} {nothing} [] {.(Γ₀ ++ Δ)} {f = f} refl (⊗ruf {.Γ₀} {Δ} {f = f₁} {g}) | inj₁ (Γ₀ , refl , refl) = ~ scut⊗r f f₁ g
    cong-ccut2 {true} {nothing} [] {.(Γ₀ ++ Δ)} {f = f} refl (⊗ruf {.Γ₀} {Δ} {f = f₁} {g}) | inj₁ (Γ₀ , refl , refl) = ⊗ruf ∙ uf (⊗rIl ∙ Il (~ scut⊗r f f₁ g)) 
    cong-ccut2 {_}{just x} [] {.(Γ₀ ++ Δ)} {f = f} refl (⊗ruf {.Γ₀} {Δ} {f = f₁} {g}) | inj₁ (Γ₀ , refl , refl) = ⊗ruf ∙ uf (~ scut⊗r f f₁ g)
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
    cong-ccut2 Δ₀ {Δ'} r (⊗c Γ Δ p) with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    cong-ccut2 {b}{S}{Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} refl (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ p) | inj₁ (Γ₀ , refl , refl) = ⊗c (Δ₀ ++ asCxt b S Γ ++ Γ₀) Δ ( cong-ccut2 Δ₀ refl p )
    cong-ccut2 .Γ {.Δ} {f = f} refl (⊗c Γ Δ p) | inj₂ ([] , refl , refl) = cong-let⊗2 Γ Δ f p
    cong-ccut2 {b}{S} {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} refl (⊗c Γ .(Γ₀ ++ _ ∷ Δ') p) | inj₂ (_ ∷ Γ₀ , refl , refl) = ⊗c Γ (Γ₀ ++ asCxt b S Γ₁ ++ Δ') (cong-ccut2 (Γ ++ _ ∷ _ ∷ Γ₀) refl p)
    cong-ccut2 {false} {nothing} [] {Δ'} {f = f} refl (uf⊗c1 {f = f₁}) = ~ let⊗-[] Δ' f f₁
    cong-ccut2 {true} {nothing} [] {Δ'} {f = f} refl (uf⊗c1 {f = f₁}) = ~ let⊗-[]-true Δ' f f₁ 
    cong-ccut2 {_}{just x} [] {Δ'} {f = f} refl (uf⊗c1 {f = f₁}) = ~ let⊗-[]-j Δ' f f₁ 
    cong-ccut2 (_ ∷ Δ₀) refl uf⊗c1 = uf⊗c1
    cong-ccut2 Δ₀ {Δ'} r (⊗c⊗c {Γ = Γ} {Δ} {Λ}) with cases++ Δ₀ (Γ ++ _ ∷ Δ) Δ' (_ ∷ Λ) r
    cong-ccut2 Δ₀ {.(Γ₀ ++ _ ∷ Λ)} r (⊗c⊗c {Γ = Γ} {Δ} {Λ}) | inj₁ (Γ₀ , p , refl) with cases++ Δ₀ Γ Γ₀ (_ ∷ Δ) p
    cong-ccut2 {b}{S}{Γ = Γ} Δ₀ {.((Γ₀' ++ _ ∷ Δ) ++ _ ∷ Λ)} {A} refl (⊗c⊗c {Γ = .(Δ₀ ++ A ∷ Γ₀')} {Δ} {Λ} {J = J}{J'}{K}{K'}) | inj₁ (.(Γ₀' ++ _ ∷ Δ) , refl , refl) | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Δ ++ K ⊗ K' ∷ Λ)  A | cases++-inj₁ Δ₀ Γ₀' (J ⊗ J' ∷ Δ ++ K ∷ K' ∷ Λ) A | cases++-inj₁ Δ₀ (Γ₀' ++ J ∷ J' ∷ Δ) (K ⊗ K' ∷ Λ) A =
      ⊗c⊗c {Γ = Δ₀ ++ asCxt b S Γ ++ Γ₀'}{Δ}{Λ}
    cong-ccut2 Δ₀ {.(Γ₀ ++ _ ∷ Λ)}  {f = f'} refl (⊗c⊗c {Γ = .Δ₀} {.Γ₀} {Λ} {J = J}{J'}{K}{K'} {f = f}) | inj₁ (Γ₀ , refl , refl) | inj₂ ([] , refl , refl) 
      rewrite cases++-inj₂ [] Δ₀ (Γ₀ ++ K ⊗ K' ∷ Λ) (J ⊗ J') | cases++-inj₂ [] Δ₀ (Γ₀ ++ K ∷ K' ∷ Λ) (J ⊗ J') = let⊗-⊗c1 Δ₀ Γ₀ Λ f' f
    cong-ccut2 {b}{S}{Γ = Γ₁} .(Γ ++ _ ∷ Γ₀') {.(Γ₀ ++ _ ∷ Λ)} {A} refl (⊗c⊗c {Γ = Γ} {.(Γ₀' ++ A ∷ Γ₀)} {Λ} {J = J}{J'}{K}{K'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (_ ∷ Γ₀' , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Γ₀ ++ K ⊗ K' ∷ Λ) A | cases++-inj₁ (Γ ++ J ∷ J' ∷ Γ₀') Γ₀ (K ⊗ K' ∷ Λ) A | cases++-inj₂ (J ⊗ J' ∷ Γ₀') Γ (Γ₀ ++ K ∷ K' ∷ Λ) A =
      ⊗c⊗c {Γ = Γ}{Γ₀' ++ asCxt b S Γ₁ ++ Γ₀}{Λ}
    cong-ccut2 .(Γ ++ _ ∷ Δ) {.Λ} {f = f} refl (⊗c⊗c {Γ = Γ} {Δ} {Λ} {J = J}{J'}{K}{K'} {f = g}) | inj₂ ([] , refl , refl) 
      rewrite cases++-inj₂ (J ⊗ J' ∷ Δ) Γ Λ (K ⊗ K') | cases++-inj₂ [] (Γ ++ J ∷ J' ∷ Δ) Λ (K ⊗ K')  = ~ let⊗-⊗c2 Γ Δ Λ f g 
    cong-ccut2 {b}{S}{Γ = Γ₁} .(Γ ++ _ ∷ Δ ++ _ ∷ Γ₀) {Δ'} {A} refl (⊗c⊗c {Γ = Γ} {Δ} {.(Γ₀ ++ A ∷ Δ')} {J = J}{J'}{K}{K'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Δ ++ K ⊗ K' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (J ⊗ J' ∷ Δ ++ K ∷ K' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (K ⊗ K' ∷ Γ₀) (Γ ++ J ∷ J' ∷ Δ) Δ' A =
      ⊗c⊗c {Γ = Γ}{Δ}{Γ₀ ++ asCxt b S Γ₁ ++ Δ'}
    cong-ccut2 Δ₀ {Δ'} r (uf⊗c2 {Γ}{Δ}) with cases++ Δ₀ (_ ∷ Γ) Δ' (_ ∷ Δ) r
    cong-ccut2 {false} {nothing} [] {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} {f = f} refl (uf⊗c2 {.Γ₀} {Δ} {f = f₁}) | inj₁ (Γ₀ , refl , refl) = scut-⊗c Γ₀ Δ f f₁
    cong-ccut2 {true} {nothing} {Γ = Γ} [] {.(Γ₀ ++ _ ⊗ _ ∷ Δ)} {f = f} refl (uf⊗c2 {.Γ₀} {Δ} {f = f₁}) | inj₁ (Γ₀ , refl , refl) =
      uf (Il (scut-⊗c Γ₀ Δ f f₁)) ∙ (uf (Il⊗c {Γ = Γ ++ Γ₀}) ∙ uf⊗c2 {Γ = Γ ++ Γ₀}{Δ}) 
    cong-ccut2 {_}{just x} {Γ = Γ} [] {.(Γ₀ ++ _ ∷ Δ)} {f = f} refl (uf⊗c2 {.Γ₀} {Δ} {f = f₁}) | inj₁ (Γ₀ , refl , refl) = uf (scut-⊗c Γ₀ Δ f f₁) ∙ uf⊗c2 {Γ = Γ ++ Γ₀}
    cong-ccut2 {b}{S}{Γ = Γ} (x ∷ Δ₀) {.(Γ₀ ++ _ ∷ Δ)} {A} refl (uf⊗c2 {.(Δ₀ ++ A ∷ Γ₀)} {Δ} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Δ) A = uf⊗c2 {Γ = Δ₀ ++ asCxt b S Γ ++ Γ₀}
    cong-ccut2 .(_ ∷ Γ) {.Δ} {f = f₁} refl (uf⊗c2 {Γ} {Δ} {J = J}{J'} {f = f}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Γ Δ (J ⊗ J') = ~ let⊗-uf Γ Δ f₁ f
    cong-ccut2 .(_ ∷ Γ ++ _ ∷ Γ₀) {Δ'} {A} refl (uf⊗c2 {Γ} {.(Γ₀ ++ A ∷ Δ')} {J = J}{J'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ Δ' A = uf⊗c2
    cong-ccut2 Δ₀ {Δ'} r (Il⊗c {Γ} {Δ}) with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    cong-ccut2 {b}{S} {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} refl (Il⊗c {.(Δ₀ ++ _ ∷ Γ₀)} {Δ}) | inj₁ (Γ₀ , refl , refl) = Il⊗c {Γ = Δ₀ ++ asCxt b S Γ ++ Γ₀}
    cong-ccut2 Δ₀ {.Δ} {f = f₁} refl (Il⊗c {.Δ₀} {Δ} {f = f}) | inj₂ ([] , refl , refl) = ~ let⊗-Il Δ₀ Δ f₁ f 
    cong-ccut2 {b}{S} {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} refl (Il⊗c {Γ} {.(Γ₀ ++ _ ∷ Δ')}) | inj₂ (_ ∷ Γ₀ , refl , refl) = Il⊗c 
    cong-ccut2 Δ₀ {Δ'} r (⊗l⊗c {Γ} {Δ}) with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
    cong-ccut2 {b}{S} {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} {A} refl (⊗l⊗c {.(Δ₀ ++ A ∷ Γ₀)} {Δ} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Δ) A = ⊗l⊗c {Γ = Δ₀ ++ asCxt b S Γ ++ Γ₀}
    cong-ccut2 Δ₀ {.Δ} {f = f₁} refl (⊗l⊗c {.Δ₀} {Δ} {J = J}{J'} {f = f}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ [] Δ₀ Δ (J ⊗ J') = ~ let⊗-⊗l Δ₀ Δ f₁ f 
    cong-ccut2 .(Γ ++ _ ∷ Γ₀) {Δ'} {A} refl (⊗l⊗c {Γ} {.(Γ₀ ++ _ ∷ Δ')} {J = J}{J'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ Δ' A = ⊗l⊗c
    cong-ccut2 Δ₀ {Δ'} r (⊗r⊗c1 {Γ = Γ} {Γ'} {Δ}) with cases++ Δ₀ Γ Δ' (_ ∷ Γ' ++ Δ) r
    cong-ccut2 {b}{S} {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Γ' ++ Δ)} {A} refl (⊗r⊗c1 {Γ = .(Δ₀ ++ A ∷ Γ₀)} {Γ'} {Δ} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Γ₀ ++ J ⊗ J' ∷ Γ') Δ A | cases++-inj₁ Δ₀ (Γ₀ ++ J ∷ J' ∷ Γ') Δ A | cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Γ') A = ⊗r⊗c1 {Γ = Δ₀ ++ asCxt b S Γ ++ Γ₀}
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
    cong-ccut2 {b}{S}{Γ = Γ₁} .(Γ ++ Γ₀') {.(Γ₀ ++ _ ∷ Δ'')} {A} refl (⊗r⊗c2 {Γ = Γ} {.(Γ₀' ++ _ ∷ Γ₀)} {Δ''} {J = J}{J'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl)
      rewrite cases++-inj₂ Γ₀' Γ (Γ₀ ++ J ⊗ J' ∷ Δ'') A | cases++-inj₂ Γ₀' Γ (Γ₀ ++ J ∷ J' ∷ Δ'') A | cases++-inj₁ Γ₀' Γ₀ (J ⊗ J' ∷ Δ'') A = ⊗r⊗c2 {Γ = Γ}{Γ₀' ++ asCxt b S Γ₁ ++ Γ₀}
    cong-ccut2 .(Γ ++ Δ) {.Δ''} {A} {f = f} refl (⊗r⊗c2 {Γ = Γ} {Δ} {Δ''} {J = J}{J'} {f = f₁}{g}) | inj₂ ([] , refl , refl)
      rewrite cases++-inj₂ Δ Γ Δ'' (J ⊗ J') | cases++-inj₂ [] Δ Δ'' (J ⊗ J') = ~ let⊗-⊗r2 Δ Δ'' f f₁ g 
    cong-ccut2 .(Γ ++ Δ ++ _ ∷ Γ₀) {Δ'} {A} refl (⊗r⊗c2 {Γ = Γ} {Δ} {.(Γ₀ ++ _ ∷ Δ')} {J = J}{J'}) | inj₂ (_ ∷ Γ₀ , refl , refl)
      rewrite cases++-inj₂ (Δ ++ J ⊗ J' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (Δ ++ J ∷ J' ∷ Γ₀) Γ Δ' A | cases++-inj₂ (J ⊗ J' ∷ Γ₀) Δ Δ' A = ⊗r⊗c2

cong-scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
             {f g : S ∣ Γ ⊢ A}  → {h k : just A ∣ Δ' ⊢ C} →
             f ≗ g → h ≗ k → scut f h ≗ scut g k
cong-scut {g = g} p q = cong-scut1 p ∙ cong-scut2 g q             

cong-ccut : (b : Bool) {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
             {f f' : nothing ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C}  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
             f ≗ f' → g ≗ g' → ccut b Δ₀ f g r ≗ ccut b Δ₀ f' g' r
cong-ccut b Δ₀ {g = g} r p q = cong-ccut1 Δ₀ g r p  ∙ cong-ccut2 Δ₀ r q
