
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

-- the free right-normal skew-monoidal category

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
  ρ-1 : {A : Fma} → A ⊗ I ⇒ A

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

  -- ρ iso
  ρρ-1 : {A : Fma} → ρ ∘ ρ-1 ≐ id {A ⊗ I}
  ρ-1ρ : {A : Fma} → ρ-1 ∘ ρ ≐ id {A}

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

nρ-1 : {A B : Fma} {f : A ⇒ B} → ρ-1 ∘ f ⊗ id ≐ f ∘ ρ-1
nρ-1 {f = f} =
  proof≐
    ρ-1 ∘ f ⊗ id
  ≐⟨ rid ⟩
    ρ-1 ∘ f ⊗ id ∘ id
  ≐⟨ ~ (refl ∘ ρρ-1) ⟩
    ρ-1 ∘ f ⊗ id ∘ (ρ ∘ ρ-1)
  ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩
    ρ-1 ∘ (f ⊗ id ∘ ρ) ∘ ρ-1
  ≐⟨ ~ (refl ∘ nρ) ∘ refl ⟩
    ρ-1 ∘ (ρ ∘ f) ∘ ρ-1
  ≐⟨ ~ (ass ∘ refl) ⟩
    ρ-1 ∘ ρ ∘ f ∘ ρ-1
  ≐⟨ ρ-1ρ ∘ refl ∘ refl ⟩
    id ∘ f ∘ ρ-1
  ≐⟨ ass ∙ lid ⟩
    f ∘ ρ-1
  qed≐

l≐ρ-1 : l ≐ ρ-1 {I}
l≐ρ-1 =
  rid
  ∙ (refl ∘ ~ ρρ-1)
  ∙ ~ ass
  ∙ (lρ ∘ refl)
  ∙ lid

ρα-1 : {A B : Fma} → id ⊗ ρ-1 ∘ α ≐ ρ-1 {A ⊗ B}
ρα-1 =
  rid
  ∙ (refl ∘ ~ ρρ-1)
  ∙ ~ ass
  ∙ (ass ∙ (refl ∘ αρ) ∙ ~ f⊗∘ ∙ (lid ⊗ ρ-1ρ ∙ f⊗id) ∘ refl)
  ∙ lid

-- ===========================================================

-- closed formula,  i.e. not containing atomic formulas

data isCl : Fma → Set where
  isI : isCl I
  is⊗ : ∀{J J'} → isCl J → isCl J' → isCl (J ⊗ J')

-- Variants of ρ and ρ-1, with I replaced by any closed formula

ρJ : {A J : Fma} → isCl J → A ⇒ A ⊗ J
ρJ isI = ρ
ρJ (is⊗ cJ cJ') = id ⊗ ρJ cJ' ∘ ρJ cJ

ρJ-1 : {A J : Fma} → isCl J → A ⊗ J ⇒ A
ρJ-1 isI = ρ-1
ρJ-1 (is⊗ cJ cJ') = ρJ-1 cJ ∘ id ⊗ ρJ-1 cJ'

-- A particular instance of a map in the opposite direction of α, in
-- which the right-most formula is closed.

-- -- Notice that a general inverse of α is not derivable in the
-- -- right-normal case.

αJ-1 : {A B J : Fma} → isCl J → A ⊗ (B ⊗ J) ⇒ (A ⊗ B) ⊗ J
αJ-1 cJ = ρJ cJ ∘ id ⊗ ρJ-1 cJ

-- Some derivable laws of ρJ, ρJ-1 and αJ-1.

ρJρJ-1 : {A J : Fma} (cJ : isCl J) → ρJ cJ ∘ ρJ-1 cJ ≐ id {A ⊗ J}
ρJρJ-1 isI = ρρ-1
ρJρJ-1 (is⊗ cJ cJ') =
  proof≐
    id ⊗ ρJ cJ' ∘ ρJ cJ ∘ (ρJ-1 cJ ∘ id ⊗ ρJ-1 cJ')
  ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩
    id ⊗ ρJ cJ' ∘ (ρJ cJ ∘ ρJ-1 cJ) ∘ id ⊗ ρJ-1 cJ'
  ≐⟨ refl ∘ ρJρJ-1 cJ ∘ refl ⟩
    id ⊗ ρJ cJ' ∘ id ∘ id ⊗ ρJ-1 cJ'
  ≐⟨ ~ rid ∘ refl ⟩
    id ⊗ ρJ cJ' ∘ id ⊗ ρJ-1 cJ'
  ≐⟨ ~ f⊗∘ ⟩
    (id ∘ id) ⊗ (ρJ cJ' ∘ ρJ-1 cJ')
  ≐⟨ lid ⊗ ρJρJ-1 cJ' ⟩
    id ⊗ id
  ≐⟨ f⊗id ⟩
    id
  qed≐

ρJ-1ρJ : {A J : Fma} (cJ : isCl J) → ρJ-1 cJ ∘ ρJ cJ ≐ id {A}
ρJ-1ρJ isI = ρ-1ρ
ρJ-1ρJ (is⊗ cJ cJ') =
  proof≐
    ρJ-1 cJ ∘ id ⊗ ρJ-1 cJ' ∘ (id ⊗ ρJ cJ' ∘ ρJ cJ)
  ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩
    ρJ-1 cJ ∘ (id ⊗ ρJ-1 cJ' ∘ id ⊗ ρJ cJ') ∘ ρJ cJ
  ≐⟨ refl ∘ ~ f⊗∘ ∘ refl ⟩
    ρJ-1 cJ ∘ (id ∘ id) ⊗ (ρJ-1 cJ' ∘ ρJ cJ') ∘ ρJ cJ
  ≐⟨ refl ∘ lid ⊗ ρJ-1ρJ cJ' ∘ refl ⟩
    ρJ-1 cJ ∘ id ⊗ id ∘ ρJ cJ
  ≐⟨ refl ∘ f⊗id ∙ ~ rid ∘ refl ⟩
    ρJ-1 cJ ∘ ρJ cJ
  ≐⟨ ρJ-1ρJ cJ ⟩
    id
    qed≐

αρJ : {A B J : Fma} (cJ : isCl J) → α ∘ ρJ cJ ≐ id {A} ⊗ ρJ {B} cJ
αρJ isI = αρ
αρJ (is⊗ cJ cJ') =
  proof≐
    α ∘ (id ⊗ ρJ cJ' ∘ ρJ cJ)
  ≐⟨ ~ ass ∙ (refl ∘ (~ f⊗id) ⊗ refl ∘ refl) ⟩
    α ∘ id ⊗ id ⊗ ρJ cJ' ∘ ρJ cJ
  ≐⟨ nα ∘ refl ⟩
    id ⊗ (id ⊗ ρJ cJ') ∘ α ∘ ρJ cJ
  ≐⟨ ass ⟩
    id ⊗ (id ⊗ ρJ cJ') ∘ (α ∘ ρJ cJ)
  ≐⟨ refl ∘ αρJ cJ ⟩
    id ⊗ (id ⊗ ρJ cJ') ∘ id ⊗ ρJ cJ
  ≐⟨ ~ f⊗∘ ∙ lid ⊗ refl ⟩
    id ⊗ (id ⊗ ρJ cJ' ∘ ρJ cJ)
  qed≐


nρJ : {A B J : Fma} (cJ : isCl J) {f : A ⇒ B}
  → ρJ cJ ∘ f ≐ f ⊗ id ∘ ρJ cJ
nρJ isI = nρ
nρJ (is⊗ cJ cJ') =
  ass
  ∙ (refl ∘ nρJ cJ)
  ∙ ~ ass
  ∙ (id⊗swap ∘ refl)
  ∙ ass

nρJ-1 : {A B J : Fma} (cJ : isCl J) {f : A ⇒ B}
  → ρJ-1 cJ ∘ (f ⊗ id) ≐ f ∘ ρJ-1 cJ
nρJ-1 cJ =
  refl ∘ (rid ∙ (refl ∘ ~ ρJρJ-1 cJ) ∙ ~ ass  ∙ (~ nρJ cJ ∘ refl) ∙ ass)
  ∙ ~ ass
  ∙ (ρJ-1ρJ cJ ∘ refl)
  ∙ lid 

ααJ-1 : {A B J : Fma} (cJ : isCl J) 
  → α ∘ αJ-1 {A}{B} cJ ≐ id 
ααJ-1 cJ =
  proof≐
    α ∘ (ρJ cJ ∘ id ⊗ ρJ-1 cJ)
  ≐⟨ ~ ass ⟩
    α ∘ ρJ cJ ∘ id ⊗ ρJ-1 cJ
  ≐⟨ αρJ cJ ∘ refl ⟩
    id ⊗ ρJ cJ ∘ id ⊗ ρJ-1 cJ
  ≐⟨ ~ f⊗∘ ⟩
    (id ∘ id) ⊗ (ρJ cJ ∘ ρJ-1 cJ)
  ≐⟨ lid ⊗ ρJρJ-1 cJ ⟩
    id ⊗ id
  ≐⟨ f⊗id ⟩
    id
  qed≐


αJ-1α : {A B J : Fma} (cJ : isCl J)
  → αJ-1 {A}{B} cJ ∘ α ≐ id 
αJ-1α cJ =
  proof≐
    ρJ cJ ∘ id ⊗ ρJ-1 cJ ∘ α
  ≐⟨ ass ⟩
    ρJ cJ ∘ (id ⊗ ρJ-1 cJ ∘ α)
  ≐⟨ refl ∘ (rid ∙ (refl ∘ ~ ρJρJ-1 cJ ∙ (~ ass ∙ (ass ∘ refl)))) ⟩
    ρJ cJ ∘ (id ⊗ ρJ-1 cJ ∘ (α ∘ ρJ cJ) ∘ ρJ-1 cJ)
  ≐⟨ refl ∘ (refl ∘ αρJ cJ ∘ refl) ⟩
    ρJ cJ ∘ (id ⊗ ρJ-1 cJ ∘ id ⊗ ρJ cJ ∘ ρJ-1 cJ)
  ≐⟨ refl ∘ (~ f⊗∘ ∘ refl ∙ (lid ⊗ ρJ-1ρJ cJ ∙ f⊗id ∘ refl)) ⟩
    ρJ cJ ∘ (id ∘ ρJ-1 cJ)
  ≐⟨ refl ∘ lid ⟩
    ρJ cJ ∘ ρJ-1 cJ 
  ≐⟨ ρJρJ-1 cJ ⟩
    id
  qed≐

nαJ-1 : {A B C D J : Fma} (cJ : isCl J) {f : A ⇒ D} {g : B ⇒ C}
  → αJ-1 cJ ∘ f ⊗ (g ⊗ id) ≐ f ⊗ g ⊗ id ∘ αJ-1 cJ
nαJ-1 cJ {f} {g} =
  proof≐
    ρJ cJ ∘ id ⊗ ρJ-1 cJ ∘ f ⊗ (g ⊗ id)
  ≐⟨ ass ∙ (refl ∘ (~ f⊗∘ ∙ (lid ∙ rid) ⊗ refl)) ⟩
    ρJ cJ ∘ (f ∘ id) ⊗ (ρJ-1 cJ ∘ g ⊗ id)
  ≐⟨ refl ∘ refl ⊗ nρJ-1 cJ ⟩
    ρJ cJ ∘ (f ∘ id) ⊗ (g ∘ ρJ-1 cJ)
  ≐⟨ refl ∘ f⊗∘ ⟩
    ρJ cJ ∘ (f ⊗ g ∘ id ⊗ ρJ-1 cJ)
  ≐⟨ ~ ass ⟩
    ρJ cJ ∘ f ⊗ g ∘ id ⊗ ρJ-1 cJ
  ≐⟨ nρJ cJ ∘ refl ⟩
    f ⊗ g ⊗ id ∘ ρJ cJ ∘ id ⊗ ρJ-1 cJ
  ≐⟨ ass ⟩
    f ⊗ g ⊗ id ∘ (ρJ cJ ∘ id ⊗ ρJ-1 cJ)
  qed≐


αααJ-1 : ∀ {A B C J} (cJ : isCl J)
  → id {A} ⊗ αJ-1 {B}{C} cJ ∘ α ≐ α ∘ α ⊗ id ∘ αJ-1 cJ
αααJ-1 cJ =
  rid
  ∙ (refl ∘ ~ ααJ-1 cJ)
  ∙ (~ ass ∙ (ass ∘ refl))
  ∙ (refl ∘ ααα ∘ refl)
  ∙ (~ ass ∙ (~ f⊗∘ ∙ (lid ⊗ αJ-1α cJ ∙ f⊗id) ∘ refl ∙ lid) ∘ refl)



