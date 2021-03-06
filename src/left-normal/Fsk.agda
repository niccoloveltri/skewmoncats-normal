module Fsk where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- generating objects At ("atomic formulae")

postulate At : Set

-- =======================================================================

-- the free left-normal skew-monoidal category

-- -- objects Fma ("formulae")

infixl 25 _⊗_

data Fma : Set where
  ` : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma

infix 15 _⇒_
infixl 20 _∘_

data _⇒_ : Fma → Fma → Set where
  id : {A : Fma} → A ⇒ A
  _∘_ : {A B C : Fma} → B ⇒ C → A ⇒ B → A ⇒ C
  _⊗_ : {A B C D : Fma} → A ⇒ B → C ⇒ D → A ⊗ C ⇒ B ⊗ D 
  l : {A : Fma} → I ⊗ A ⇒ A
  ρ : {A : Fma} → A ⇒ A ⊗ I
  α : {A B C : Fma} → (A ⊗ B) ⊗ C ⇒ A ⊗ (B ⊗ C)
  l-1 : {A : Fma} → A ⇒ I ⊗ A

infix 15 _≐_
infixl 20 _∙_
infix 21 ~_

data _≐_ : {A B : Fma} → A ⇒ B → A ⇒ B → Set where
  -- ≐ equivalence and congruence
  refl : {A B : Fma} {f : A ⇒ B} → f ≐ f
  ~_ : {A B : Fma} {f g : A ⇒ B} → f ≐ g → g ≐ f
  _∙_ : {A B : Fma} {f g h : A ⇒ B} → f ≐ g → g ≐ h → f ≐ h
  _∘_ : {A B C : Fma} {f g : B ⇒ C} {h k : A ⇒ B} →
                         f ≐ g → h ≐ k → f ∘ h ≐ g ∘ k
  _⊗_ : {A B C D : Fma} {f g : A ⇒ C} {h k : B ⇒ D} →
                         f ≐ g → h ≐ k → f ⊗ h ≐ g ⊗ k
  -- id, ∘ category
  lid : {A B : Fma} {f : A ⇒ B} → id ∘ f ≐ f
  rid : {A B : Fma} {f : A ⇒ B} → f ≐ f ∘ id
  ass : {A B C D : Fma} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
       → f ∘ g ∘ h ≐ f ∘ (g ∘ h)
  -- ⊗ functorial
  f⊗id : {A B : Fma} → id {A} ⊗ id {B} ≐ id
  f⊗∘ : {A B C D E F : Fma} {f : A ⇒ C} {g : B ⇒ D} {h : C ⇒ E} {k : D ⇒ F} →  
                    (h ∘ f) ⊗ (k ∘ g) ≐ h ⊗ k ∘ f ⊗ g
  -- l, ρ, α, s natural
  nl : {A B : Fma} {f : A ⇒ B} → l ∘ id ⊗ f ≐ f ∘ l
  nρ : {A B : Fma} {f : A ⇒ B} → ρ ∘ f ≐ f ⊗ id ∘ ρ 
  nα : {A B C D E F : Fma} {f : A ⇒ D} {g : B ⇒ E} {h : C ⇒ F} → 
                       α ∘ f ⊗ g ⊗ h ≐ f ⊗ (g ⊗ h) ∘ α

  -- skew monoidality
  lρ : l ∘ ρ ≐ id 
  lαρ : {A B : Fma} → id {A ⊗ B} ≐ id ⊗ l ∘ α ∘ ρ ⊗ id
  lα :  {A B : Fma} → l ∘ α ≐ l {A} ⊗ id {B}
  αρ : {A B : Fma} → α ∘ ρ ≐ id {A} ⊗ ρ {B}
  ααα : {A B C D : Fma} → 
         α ∘ α ≐ id {A} ⊗ α {B}{C}{D} ∘ (α ∘ α ⊗ id)

  -- l iso
  ll-1 : ∀{A} → l ∘ l-1 ≐ id {A}
  l-1l : ∀{A} → l-1 ∘ l ≐ id {I ⊗ A}

refl≐' : {A B : Fma}{f g : A ⇒ B} → f ≡ g → f ≐ g
refl≐' refl = refl

-- equational reasoning sugar for ≐

infix 4 _≐'_
infix 1 proof≐_
infixr 2 _≐⟨_⟩_
infix 3 _qed≐

data _≐'_ {A B : Fma} (f g : A ⇒ B) : Set where
  relto :  f ≐ g → f ≐' g

proof≐_ : {A B : Fma} {f g : A ⇒ B} → f ≐' g → f ≐ g
proof≐ relto p = p

_≐⟨_⟩_ :  {A B : Fma} (f : A ⇒ B) {g h : A ⇒ B} → f ≐ g → g ≐' h → f ≐' h 
_ ≐⟨ p ⟩ relto q = relto (p ∙ q)

_qed≐  :  {A B : Fma} (f : A ⇒ B) → f ≐' f
_qed≐ _ = relto refl

-- some derivable laws

id⊗swap : {A B C D : Fma}
  → {f : A ⇒ B} {g : C ⇒ D}
  → id ⊗ f ∘ g ⊗ id ≐ g ⊗ id ∘ id ⊗ f
id⊗swap {f = f}{g} =
  proof≐
    id ⊗ f ∘ g ⊗ id
  ≐⟨ ~ f⊗∘ ⟩
    (id ∘ g) ⊗ (f ∘ id)
  ≐⟨ lid ⊗ (~ rid) ⟩
    g ⊗ f
  ≐⟨ rid ⊗ (~ lid) ⟩
    (g ∘ id) ⊗ (id ∘ f)
  ≐⟨ f⊗∘ ⟩
    g ⊗ id ∘ id ⊗ f
  qed≐

nl-1 : {A B : Fma} {f : A ⇒ B} → l-1 ∘ f ≐ id ⊗ f ∘ l-1
nl-1 {f = f} =
  proof≐
    l-1 ∘ f
  ≐⟨ rid ⟩
    l-1 ∘ f ∘ id
  ≐⟨ ~ (refl ∘ ll-1) ⟩
    l-1 ∘ f ∘ (l ∘ l-1)
  ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩
    l-1 ∘ (f ∘ l) ∘ l-1
  ≐⟨ ~ (refl ∘ nl) ∘ refl ⟩
    l-1 ∘ (l ∘ id ⊗ f) ∘ l-1
  ≐⟨ ~ ass ∘ refl ⟩
    l-1 ∘ l ∘ id ⊗ f ∘ l-1
  ≐⟨ l-1l ∘ refl ∘ refl ⟩
    id ∘ id ⊗ f ∘ l-1
  ≐⟨ ass ∙ lid ⟩
    id ⊗ f ∘ l-1
  qed≐
