
module Complete where

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

-- ====================================================================

-- The completeness map, interpreting categorical derivations as
-- focused derivations.

cmplt : {A B : Fma} → A ⇒ B → just A ∣ [] ⊢L B
cmplt id = axL
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊗ g) = ⊗l (⊗rL (cmplt f) (uf (cmplt g)))
cmplt l = ⊗l (Il (uf axL))
cmplt ρ = ⊗rL axL (switch-not Ir)
cmplt α = ⊗l (⊗l (⊗rL axL (uf (⊗rL axL (uf axL)))))
cmplt l-1 = ⊗r[]L (switch-not Ir) axL

