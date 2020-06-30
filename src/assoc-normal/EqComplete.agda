{-# OPTIONS --rewriting #-}

module EqComplete where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk
open import Complete
open import Cuts
open import MulticatLaws1
open import MulticatLaws2

-- ====================================================================

-- The completeness map send ≐-related derivations to ≗-related
-- derivations.

cong-cmplt : ∀{A C} {f g : A ⇒ C} → f ≐ g → cmplt f ≗ cmplt g
cong-cmplt refl = refl
cong-cmplt (~ p) = ~ cong-cmplt p
cong-cmplt (p ∙ p₁) = cong-cmplt p ∙ cong-cmplt p₁
cong-cmplt (p ∘ p₁) = cong-scut (cong-cmplt p₁) (cong-cmplt p)
cong-cmplt (p ⊗ p₁) = ⊗l (⊗r (cong-cmplt p) (uf (cong-cmplt p₁)))
cong-cmplt lid = ≡-to-≗ (scut-unit _)
cong-cmplt rid = refl
cong-cmplt (ass {f = f} {g} {h}) = 
  scut-ass-scut (cmplt h) (cmplt g) (cmplt f)
cong-cmplt f⊗id = ~ ax⊗
cong-cmplt (f⊗∘ {f = f} {g} {h} {k}) =
 ⊗l (~ (scut⊗r (cmplt f) (cmplt h) (uf (scut (cmplt g) (cmplt k)))))
cong-cmplt nl = ⊗l (Il (uf (≡-to-≗ (scut-unit _))))
cong-cmplt (nρ {f = f}) =
  scut⊗r (cmplt f) ax Ir ∙ ⊗r (≡-to-≗ (scut-unit _)) refl
cong-cmplt (nα {f = f} {g} {h}) = 
  ⊗l (⊗l (scut⊗r (cmplt f) ax _
  ∙ ⊗r (≡-to-≗ (scut-unit _))
       (uf (scut⊗r (cmplt g) ax _
            ∙ ⊗r (≡-to-≗ (scut-unit _))
                 (≡-to-≗ (scut-unit _))))))
cong-cmplt lρ = ~ axI
cong-cmplt lαρ = ax⊗
cong-cmplt lα = ⊗l (⊗l (Il (~ ⊗ruf) ∙ (~ ⊗rIl)) ∙ (~ ⊗r⊗l))
cong-cmplt αρ = refl
cong-cmplt ααα = refl
cong-cmplt αα-1 = 
  proof≗
    ⊗l (⊗c [] [] (⊗r ax (uf (⊗r ax (uf ax)))))
  ≗〈 ⊗l (~ ⊗r⊗c2) 〉  
    ⊗l (⊗r ax (⊗c [] [] (uf (⊗r ax (uf ax)))))
  ≗〈 ⊗l (⊗r refl (~ uf⊗c1)) 〉  
    ⊗l (⊗r ax (uf (⊗l (⊗r ax (uf ax)))))
  ≗〈 ⊗l (⊗r refl (uf (~ ax⊗))) 〉  
    ⊗l (⊗r ax (uf ax))
  ≗〈 ~ ax⊗ 〉  
    ax
  qed≗
cong-cmplt α-1α =
  proof≗
    ⊗l (⊗l (⊗r (⊗r ax (uf ax)) (uf ax)))
  ≗〈 ⊗l (~ ⊗r⊗l) 〉
    ⊗l (⊗r (⊗l (⊗r ax (uf ax))) (uf ax))
  ≗〈 ⊗l (⊗r (~ ax⊗) refl) 〉
    ⊗l (⊗r ax (uf ax))
  ≗〈 ~ ax⊗ 〉
    ax
  qed≗

