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
open import MulticatLaws
open import Sound
open import StrongComplete

-- ====================================================================

-- The completeness map is compatible with ≐

abstract
  cong-cmplt : ∀{A C} {f g : A ⇒ C} → f ≐ g → cmplt f ≡ cmplt g
  cong-cmplt refl = refl
  cong-cmplt (~ p) = sym (cong-cmplt p)
  cong-cmplt (p ∙ p₁) = trans (cong-cmplt p) (cong-cmplt p₁)
  cong-cmplt (p ∘ p₁) = cong₂ scut (cong-cmplt p₁) (cong-cmplt p)
  cong-cmplt (p ⊗ p₁) =
    cong ⊗l (cong₂ ⊗rL (cong-cmplt p) (cong uf (cong-cmplt p₁)))
  cong-cmplt lid = scut-axL2 _
  cong-cmplt rid = sym (scut-axL1 _)
  cong-cmplt (ass {f = f} {g} {h}) =
    scut-ass-scut (cmplt h) _ _ 
  cong-cmplt f⊗id = refl
  cong-cmplt (f⊗∘ {f = f} {g} {h} {k}) =
    cong ⊗l
      (trans (sym (scut-⊗rL2 (cmplt f) (cmplt h) (uf (scut (cmplt g) (cmplt k)))))
        (trans (cong (scut (cmplt f)) (sym (ccut-⊗rL2 [] (uf (cmplt g)) (cmplt h) (uf (cmplt k)) refl)))
          (sym (scut-⊗rL-⊗l (cmplt f) (uf (cmplt g)) (⊗rL (cmplt h) (uf (cmplt k)))))))
  cong-cmplt (nl {f = f}) =
    cong ⊗l (cong Il (cong uf
      (trans
        (trans (scut-⊗r[]L-⊗l-fma Ir (cmplt f) (Il (uf axL))) (scut-axL2 _))
        (sym (scut-axL1 _)))))
  cong-cmplt (nρ {f = f}) =
    trans (scut-⊗rL2 (cmplt f) _ _)
      (trans (cong₂ ⊗rL (scut-axL2 _) refl)
        (trans (sym (ccut-⊗rL2 [] (switch-not Ir) (cmplt f) (uf (Il (switch-not Ir))) refl))
          (trans (sym (scut-axL1 _))
            (sym (scut-⊗rL-⊗l axL (switch-not Ir) _)))))
  cong-cmplt (nα {f = f} {g} {h}) =
    cong ⊗l (cong ⊗l
      (trans (scut-⊗rL-⊗l (⊗rL (cmplt f) (uf (cmplt g))) _ _)
        (trans (scut-⊗rL-⊗l (cmplt f) _ _)
          (trans (cong (λ x → scut (cmplt f) (ccut [] (uf (cmplt g)) x refl)) (ccut-⊗rL2 (_ ∷ []) _ axL _ refl) )
            (trans (cong (scut (cmplt f)) (ccut-⊗rL2 [] _ axL _ refl))
              (trans (scut-⊗rL2 (cmplt f) _ _)
                (trans (cong (λ x → ⊗rL (scut (cmplt f) axL) (uf (scut (cmplt g) x))) (ccut-⊗rL2 [] _ axL _ refl))
                  (sym (trans (scut-⊗rL-⊗l axL _ _)
                    (trans (scut-axL1 _)
                      (trans (ccut-⊗rL2 [] _ (cmplt f) _ refl)
                        (cong₂ ⊗rL (sym (scut-axL2 (cmplt f)))
                                   (cong uf
                                     (trans (scut-⊗rL-⊗l axL _ _)
                                       (trans (scut-axL1 _)
                                         (trans (ccut-⊗rL2 [] _ (cmplt g) _ refl)
                                           (sym (trans (scut-⊗rL2 (cmplt g) _ _)
                                             (cong₂ ⊗rL (scut-axL2 (cmplt g))
                                                        (cong uf (trans (scut-axL2 (cmplt h)) (sym (scut-axL1 _)))))))))))))))))))))))
  cong-cmplt lρ = refl
  cong-cmplt lαρ =
    cong ⊗l (sym
      (trans (scut-⊗rL-⊗l (⊗rL axL (switch-not Ir)) _ _)
        (trans (scut-⊗rL-⊗l axL _ _)
          (trans (scut-axL1 _)
            (trans (cong (λ x → ccut [] (switch-not Ir) (ccut (I ∷ []) (uf axL) x refl) refl) (trans (scut-⊗rL-⊗l axL _ _) (trans (scut-axL1 _) (ccut-⊗rL2 [] _ axL _ refl))))
              (trans (cong (λ x → ccut [] (switch-not Ir) x refl) (ccut-⊗rL2 (I ∷ []) _ axL _ refl))
                (trans (ccut-⊗rL2 [] _ axL _ refl)
                  (cong (⊗rL axL) (cong uf (trans (scut-axL1 _)
                    (trans (scut-⊗r[]L-⊗l-fma Ir axL (Il (uf axL))) (scut-axL1 _)))))))))))) 
  cong-cmplt lα = 
    cong ⊗l (cong ⊗l (cong Il (cong uf
      (trans
         (scut-⊗r[]L-⊗l-fma Ir (⊗rL axL (uf axL)) (Il (uf (⊗l (⊗rL axL (uf axL))))))
         (trans
           (scut-⊗rL-⊗l axL (uf axL) (⊗rL axL (uf axL)))
           (trans (scut-axL1 _)
             (trans (ccut-⊗rL2 [] _ axL _ refl)
               (cong (⊗rL axL) (cong uf (scut-axL1 _))))))))))
  cong-cmplt αρ =
    cong ⊗l
      (trans (scut-⊗rL-⊗l (⊗rL axL (uf axL)) _ _)
        (trans (scut-⊗rL-⊗l axL _ _)
          (trans (scut-axL1 _)
            (trans (cong (λ x → ccut [] (uf axL) x refl) (ccut-⊗rL2 (_ ∷ []) _ axL _ refl))
              (trans (ccut-⊗rL2 [] _ axL _ refl)
                (cong (⊗rL axL) (cong uf
                  (trans (scut-axL1 _)
                    (ccut-⊗rL2 [] _ axL _ refl)))))))))
  cong-cmplt ααα =
    cong ⊗l (cong ⊗l (cong ⊗l
      (trans (scut-⊗rL-⊗l (⊗rL axL (uf axL)) _ _)
        (trans (scut-⊗rL-⊗l axL _ _)
          (trans (scut-axL1 _)
            (trans (cong (λ x → ccut [] (uf axL) x refl) (ccut-⊗rL2 (_ ∷ []) _ axL _ refl))
              (trans (ccut-⊗rL2 [] _ axL _ refl)
                (sym
                  (trans (cong (λ x → scut x (⊗l (⊗rL axL (uf (⊗l (⊗l (⊗rL axL (uf (⊗rL axL (uf axL))))))))))
                               (trans (scut-⊗rL-⊗l (⊗rL axL (uf (⊗rL axL (uf axL)))) _ _)
                                 (trans (scut-⊗rL-⊗l axL _ _)
                                   (trans (scut-axL1 _)
                                     (trans (cong (λ x → ccut [] (uf (⊗rL axL (uf axL))) x refl) (ccut-⊗rL2 (_ ∷ []) _ axL _ refl))
                                       (ccut-⊗rL2 [] _ axL _ refl))))))
                    (trans (scut-⊗rL-⊗l axL _ _)
                      (trans (scut-axL1 _)
                        (trans (ccut-⊗rL2 [] _ axL _ refl)
                          (cong (⊗rL axL) (cong uf (sym
                            (trans (scut-axL1 _)
                              (trans (ccut-⊗rL2 [] _ axL _ refl)
                                (sym
                                  (trans (cong (λ x → scut x (⊗l (⊗l (⊗rL axL (uf (⊗rL axL (uf axL)))))))
                                         (trans (scut-⊗rL-⊗l axL _ _)
                                           (trans (scut-axL1 _)
                                             (trans (cong (λ x → ccut [] (uf axL) x refl) (ccut-⊗rL2 [] _ (⊗rL axL (uf axL)) _ refl))
                                               (ccut-⊗rL1 [] _ (⊗rL axL (uf axL)) _ refl)))))
                                    (trans (scut-⊗rL-⊗l (ccut [] (uf axL) (⊗rL axL (uf axL)) refl) _ _)
                                      (trans (cong (λ x → scut x (⊗l (ccut (_ ∷ []) (uf (scut axL axL)) (⊗rL axL (uf (⊗rL axL (uf axL)))) refl))) (ccut-⊗rL2 [] (uf axL) axL (uf axL) refl))
                                        (trans (scut-⊗rL-⊗l axL _ _)
                                          (trans (scut-axL1 _)
                                            (trans (cong (λ x → ccut [] (uf (scut axL axL)) x refl) (ccut-⊗rL2 (_ ∷ []) _ axL _ refl))
                                              (trans (ccut-⊗rL2 [] _ axL _ refl)
                                                (cong (⊗rL axL) (cong uf
                                                  (sym (trans (scut-⊗rL-⊗l axL _ _)
                                                    (trans (scut-axL1 _)
                                                      (trans (ccut-⊗rL2 [] _ axL _ refl)
                                                        (sym
                                                          (trans (cong (λ x → scut x (ccut [] (uf (scut axL axL)) (⊗rL axL (uf axL)) refl)) (scut-axL1 axL))
                                                            (trans (scut-axL1 _)
                                                              (trans (ccut-⊗rL2 [] _ axL _ refl)
                                                                (cong (⊗rL axL) (cong uf (scut-axL2 (scut axL axL)))))))))))))))))))))))))))))))))))))))
  cong-cmplt ll-1 =
    trans (scut-⊗r[]L-⊗l-fma Ir axL (Il (uf axL)))
      (scut-axL1 _)
  cong-cmplt l-1l = cong ⊗l (cong Il (cong uf (scut-axL1 _)))

-- ====================================================================

-- The function strcmplt sends ≐-related derivations into equal
-- derivations

cong-strcmplt : {S : Stp}{Γ : Cxt}{C : Fma}{f g : 〈 S ∣ Γ 〉 ⇒ C} → f ≐ g →
                strcmplt {S}{Γ} f ≡ strcmplt g
cong-strcmplt {S}{Γ} p = cong (⊗l-1⋆ S Γ) (cong-cmplt p)
