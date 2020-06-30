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
open import Cuts
open import MulticatLaws

-- ====================================================================

-- The completeness map, interpreting categorical derivations as
-- sequent calculus derivations.

cmplt : {A B : Fma} → A ⇒ B → just A ∣ [] ⊢ B
cmplt id = ax
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊗ g) = ⊗l (⊗r (cmplt f) (uf (cmplt g)))
cmplt l = ⊗l (Il (uf ax))
cmplt ρ = ⊗r ax Ir
cmplt α = ⊗l (⊗l (⊗r ax (uf (⊗r ax (uf ax)))))
cmplt ρ-1 = ⊗l (Ic [] [] ax)

-- ====================================================================

