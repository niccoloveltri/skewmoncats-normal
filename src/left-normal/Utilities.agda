{-# OPTIONS --rewriting #-}

module Utilities where

open import Data.Empty
open import Data.Maybe
open import Data.Sum 
open import Data.List
open import Data.Product 
open import Relation.Binary.PropositionalEquality


{-# BUILTIN REWRITE _≡_ #-}

-- Some lemmata about lists for reasoning about contexts

++ru : {X : Set} → (xs : List X) → xs ++ [] ≡ xs
++ru [] = refl
++ru (x ∷ xs) = cong (_∷_ x) (++ru xs) 

++ass : {X : Set} → (xs : List X) → {ys zs : List X} → 
           (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++ass [] = refl
++ass (x ∷ xs) = cong (_∷_ x) (++ass xs)

{-# REWRITE ++ass #-}
{-# REWRITE ++ru #-}

-- We used Agda rewriting feature to turn the propositional equalities
-- ++ass and ++ru (and a few more in the rest of the formalization)
-- into judgemental equalities. This is not necessary, but it makes
-- much easier expressing and proving e.g. the generalized
-- multicategory laws in MulticatLaws.agda.

inj∷ : {X : Set} → {x y : X} → {xs ys : List X} → 
           x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
inj∷ refl = refl , refl

[]disj∷ : {X : Set} → (xs : List X) → {ys : List X} → {x : X} →  
             [] ≡ xs ++ x ∷ ys → ⊥
[]disj∷ [] ()
[]disj∷ (x ∷ xs) ()

cases∷ : {X : Set} → (xs : List X) → {ys ys' : List X} → {x x' : X} → 
   x' ∷ ys' ≡ xs ++ x ∷ ys → 
        (x ≡ x' × xs ≡ [] × ys ≡ ys')  
        ⊎ Σ (List X) 
               (λ xs₀  → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ x' ∷ xs₀) 
cases∷ [] refl = inj₁ (refl , refl , refl)
cases∷ (x₀ ∷ xs) {ys} {.(xs ++ x ∷ ys)} {x} {.x₀} refl = inj₂ (xs , refl , refl)

cases++ : {X : Set} → (xs xs' ys ys' : List X) → {x : X} → 
   xs' ++ ys' ≡ xs ++ x ∷ ys → 
       Σ (List X) (λ xs₀ → xs' ≡ xs ++ x ∷ xs₀ × ys ≡ xs₀ ++ ys')  
     ⊎ Σ (List X) (λ xs₀ → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ xs' ++ xs₀) 
cases++ xs [] _ _ refl = inj₂ (xs , refl , refl)
cases++ [] (x' ∷ xs') _ _ refl = inj₁ (xs' , refl , refl)
cases++ (x₀ ∷ xs) (x' ∷ xs') ys ys' {x} p with inj∷ p
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q with cases++ xs xs' ys ys' q 
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q | inj₁ (xs₀ , r , r') = inj₁ (xs₀ , cong₂ _∷_ refl r , r')
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q | inj₂ (xs₀ , r , r') = inj₂ (xs₀ , r , cong₂ _∷_ refl r')

cases++2 : {X : Set} → (xs xs' ys ys' : List X) → {x y z : X} → 
   xs' ++ y ∷ z ∷ ys' ≡ xs ++ x ∷ ys → 
       Σ (List X) (λ xs₀ → xs' ≡ xs ++ x ∷ xs₀ × ys ≡ xs₀ ++ y ∷ z ∷ ys')
     ⊎ Σ (List X) (λ xs₀ → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ xs' ++ y ∷ z ∷ xs₀)
     ⊎ xs' ≡ xs × y ≡ x × z ∷ ys' ≡ ys
     ⊎ ys' ≡ ys × z ≡ x × xs ≡ xs' ++ y ∷ []
cases++2 xs xs' ys ys' {y = y}{z} r with cases++ xs xs' ys (y ∷ z ∷ ys') r
cases++2 xs ._ ._ ys' refl | inj₁ (xs₀ , refl , refl) = inj₁ (xs₀ , refl , refl)     
cases++2 ._ xs' ys ys' r | inj₂ (xs₀ , p , refl) with cases∷ xs₀ p
cases++2 ._ xs' ._ ys' r | inj₂ (.[] , refl , refl) | inj₁ (refl , refl , refl) =
  inj₂ (inj₂ (inj₁ (refl , refl , refl)))     
cases++2 ._ xs' ys ys' r | inj₂ (._ , p , refl) | inj₂ (xs₀ , s , refl) with cases∷ xs₀ s
cases++2 ._ xs' ys .ys r | inj₂ (._ , refl , refl) | inj₂ (.[] , _ , refl) | inj₁ (refl , refl , _) =
  inj₂ (inj₂ (inj₂ (refl , refl , refl)))     
cases++2 ._ xs' ys ._ r | inj₂ (._ , _ , refl) | inj₂ (._ , _ , refl) | inj₂ (xs₀ , refl , refl) = inj₂ (inj₁ (xs₀ , refl , refl))     

canc⊥ : {A : Set}{x : A}(xs ys : List A)
  → ys ≡ x ∷ xs ++ ys → ⊥
canc⊥ _ [] ()
canc⊥ [] (y ∷ ys) ()
canc⊥ (x ∷ xs) (y ∷ ys) p with inj∷ p
... | (refl , q) = canc⊥ (xs ++ y ∷ []) ys q

canc⊥2 : {A : Set}{x : A}(xs : List A){ys : List A}
  → xs ≡ xs ++ x ∷ ys → ⊥
canc⊥2 [] ()
canc⊥2 (x ∷ xs) p = canc⊥2 xs (proj₂ (inj∷ p))

canc⊥3 : {A : Set}{x : A}(xs ys zs : List A)
  → ys ≡ zs ++ x ∷ xs ++ ys → ⊥
canc⊥3 xs ys [] p = canc⊥ xs ys p
canc⊥3 {_} {x} xs ys (z ∷ zs) p = canc⊥ (zs ++ x ∷ xs) ys p

canc⊥4 : {A : Set}{x : A}(xs : List A){ys zs : List A}
  → xs ≡ (xs ++ zs) ++ x ∷ ys → ⊥
canc⊥4 [] {_}{zs} p = []disj∷ zs p
canc⊥4 (x ∷ xs) {zs = zs} p = canc⊥4 xs {zs = zs} (proj₂ (inj∷ p))

canc++ : {A : Set}(xs xs' : List A){ys : List A} → xs ++ ys ≡ xs' ++ ys → xs ≡ xs'
canc++ [] [] p = refl
canc++ [] (x ∷ xs') {ys} p = ⊥-elim (canc⊥ xs' ys p)
canc++ (x ∷ xs) [] {ys} p = ⊥-elim (canc⊥ xs ys (sym p))
canc++ (x ∷ xs) (x₁ ∷ xs') p with inj∷ p
canc++ (x ∷ xs) (.x ∷ xs'){ys} p | refl , q = cong (_∷_ x) (canc++ xs xs' {ys} q)

++canc : {A : Set}{xs xs' : List A}(ys : List A) → ys ++ xs ≡ ys ++ xs' → xs ≡ xs'
++canc [] p = p
++canc (x ∷ ys) p = ++canc ys (proj₂ (inj∷ p))

cases++-inj₁ : {X : Set} → (xs ys zs : List X) → (x : X) →
  cases++ xs (xs ++ x ∷ ys) (ys ++ zs) zs refl ≡ inj₁ (ys , refl , refl)
cases++-inj₁ xs ys zs x with cases++ xs (xs ++ x ∷ ys) (ys ++ zs) zs refl
cases++-inj₁ xs ys zs x | inj₁ (xs' , p , q) with canc++ ys xs' {zs} q
cases++-inj₁ xs ys zs x | inj₁ (.ys , refl , refl) | refl = refl
cases++-inj₁ xs ys zs x | inj₂ (ys' , p , q) = ⊥-elim (canc⊥3 ys zs ys' p)

cases++-inj₂ : {X : Set} → (xs xs' ys : List X) → (x : X) → 
   cases++ (xs' ++ xs) xs' ys (xs ++ x ∷ ys) refl ≡ inj₂ (xs , refl , refl)
cases++-inj₂ xs xs' ys x with cases++ (xs' ++ xs) xs' ys (xs ++ x ∷ ys) refl
cases++-inj₂ xs xs' ys x | inj₁ (xs₀ , p , q) = ⊥-elim (canc⊥3 [] ys (xs₀ ++ xs) q)
cases++-inj₂ xs xs' ys x | inj₂ (xs₀ , p , q) with ++canc {xs = xs}{xs₀} xs' q
cases++-inj₂ xs xs' ys x | inj₂ (.xs , refl , refl) | refl = refl
