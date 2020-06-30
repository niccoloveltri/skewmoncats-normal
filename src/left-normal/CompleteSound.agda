{-# OPTIONS --rewriting #-}

module CompleteSound where

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
open import MulticatLaws
open import Complete
open import StrongComplete
open import Sound
open import EqComplete

-- the function cmplt ∘ sound is equal to ⊗l⋆

mutual
  cmpltsound' : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢L C) → cmplt (sound f) ≡ ⊗l⋆ S Γ f
  cmpltsound' (uf {Γ}{A} f) =
    begin
    scut (cmplt [ l ∣ Γ ]f) (cmplt (sound f))
    ≡⟨ cong (scut (cmplt [ l ∣ Γ ]f)) (cmpltsound' f) ⟩
    scut (cmplt [ l ∣ Γ ]f) (⊗l⋆ (just A) Γ f)
    ≡⟨ cong (λ x → scut x (⊗l⋆ (just A) Γ f)) (cmplt-uf-lemma Γ l) ⟩
    scut (⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (scut axL (⊗l-1⋆ (just (t (just A))) Γ axL)))))) (⊗l⋆ (just A) Γ f) 
    ≡⟨ scut⊗l⋆ {just (I ⊗ A)}{Γ}  ⟩
    ⊗l⋆ (just (I ⊗ A)) Γ (scut (⊗l (Il (uf (scut axL (⊗l-1⋆ (just (t (just A))) Γ axL))))) (⊗l⋆ (just A) Γ {[]} f)) 
    ≡⟨ cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (cong (λ x → scut x (⊗l⋆ (just A) Γ {[]} f)) (scut-axL1 (⊗l-1⋆ (just (t (just A))) Γ axL)))))) ⟩
    ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (scut (⊗l-1⋆ (just A) Γ axL) (⊗l⋆ (just A) Γ {[]} f)))))
    ≡⟨ cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (scut⊗l-1⋆ {just A}{Γ})))) ⟩
    ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ {[]} (scut axL (⊗l⋆ (just A) Γ f))))))
    ≡⟨ cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (cong (⊗l-1⋆ (just A) Γ {[]}) (scut-axL1 _))))) ⟩
    ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ (⊗l⋆ (just A) Γ {[]} f)))))
    ≡⟨ cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (⊗l⋆-iso {just A}{Γ})))) ⟩
    ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf f)))
    ∎
  cmpltsound' {Γ = []} (Il f) = cmpltsound' f
  cmpltsound' {Γ = _ ∷ Γ} (Il f) = cmpltsound' f
  cmpltsound' (⊗l f) = cmpltsound' f
  cmpltsound' (switch-at f) = cmpltsoundR'-at f 
  cmpltsound' (switch-not f) = cmpltsoundR'-not f refl

  cmpltsoundR'-not : {Γ : Cxt} → {C : Fma} → (f : nothing ∣ Γ ⊢R C) (r : Γ ≡ [])
    → cmplt (soundR f) ≡ ⊗l⋆ nothing Γ (subst-cxt (sym r) (switch-not (subst-cxtR r f)))
  cmpltsoundR'-not Ir refl = refl
  cmpltsoundR'-not (⊗r {Γ = []} f (switch-not g)) refl =
    cong Il
      (cong (scutR Ir)
              (trans (ccut-⊗rL2 [] (switch-not Ir) (cmplt (soundR f)) (uf (cmplt (soundR g))) refl)
                     (cong₂ ⊗rL (cmpltsoundR'-not f refl) (cong (scutR Ir) (cmpltsoundR'-not g refl)))))

  cmpltsoundR'-at : {Γ : Cxt} → {X : At} {C : Fma} → (f : just X ∣ Γ ⊢R C)
    → cmplt (soundR f) ≡ ⊗l⋆ (just (` X)) Γ (switch-at f)
  cmpltsoundR'-at ax = refl
  cmpltsoundR'-at {X = X} (⊗r {Γ = Γ} {Δ} f g) =
    begin
      scut (scut (cmplt [ ρ ∣ Δ ]f) (cmplt (ψ [ ` X ∣ Γ ] I Δ))) (⊗l (⊗rL (cmplt (soundR f)) (uf (cmplt (sound g)))))
    ≡⟨ cong (λ x → scut x  (⊗l (⊗rL (cmplt (soundR f)) (uf (cmplt (sound g)))))) (cmplt-⊗rL-lemma {just (` X)}{Γ}{Δ}) ⟩
      scut ((⊗l⋆ (just (` X)) (Γ ++ Δ) (⊗rL (⊗l-1⋆ (just (` X)) Γ axL) (⊗l-1⋆ nothing Δ axL)))) (⊗l (⊗rL (cmplt (soundR f)) (uf (cmplt (sound g)))))
    ≡⟨ scut⊗l⋆ {just (` X)} {Γ ++ Δ} ⟩
      ⊗l⋆ (just (` X)) (Γ ++ Δ) (scut (⊗rL (⊗l-1⋆ (just (` X)) Γ axL) (⊗l-1⋆ nothing Δ axL))  (⊗l (⊗rL (cmplt (soundR f)) (uf (cmplt (sound g))))))
    ≡⟨ cong (⊗l⋆ (just (` X)) (Γ ++ Δ)) (scut-⊗rL-⊗l (⊗l-1⋆ (just (` X)) Γ axL) (⊗l-1⋆ nothing Δ axL) _ ) ⟩
      ⊗l⋆ (just (` X)) (Γ ++ Δ) (scut (⊗l-1⋆ (just (` X)) Γ axL) (ccut [] (⊗l-1⋆ nothing Δ axL)  (⊗rL (cmplt (soundR f)) (uf (cmplt (sound g)))) refl))
    ≡⟨ cong (⊗l⋆ (just (` X)) (Γ ++ Δ)) (cong (scut (⊗l-1⋆ (just (` X)) Γ axL)) (ccut-⊗rL2 [] (⊗l-1⋆ nothing Δ axL) (cmplt (soundR f)) (uf (cmplt (sound g))) refl)) ⟩
      ⊗l⋆ (just (` X)) (Γ ++ Δ) (scut (⊗l-1⋆ (just (` X)) Γ axL) (⊗rL (cmplt (soundR f)) (scut (⊗l-1⋆ nothing Δ axL) (cmplt (sound g)))))
    ≡⟨ cong (⊗l⋆ (just (` X)) (Γ ++ Δ)) (cong (scut (⊗l-1⋆ (just (` X)) Γ axL)) (cong₂ ⊗rL (cmpltsoundR'-at f) (cong (scut (⊗l-1⋆ nothing Δ axL)) (cmpltsound' g)))) ⟩
      ⊗l⋆ (just (` X)) (Γ ++ Δ) {[]} (scut (⊗l-1⋆ (just (` X)) Γ {[]} axL) (⊗rL (⊗l⋆ (just (` X)) Γ {[]} (switch-at f)) (scut (⊗l-1⋆ nothing Δ {[]} axL) (⊗l⋆ nothing Δ {[]} g))))
    ≡⟨ cong (⊗l⋆ (just (` X)) (Γ ++ Δ)) (scut-⊗rL2 ((⊗l-1⋆ (just (` X)) Γ {[]} axL)) _ _) ⟩
      ⊗l⋆ (just (` X)) (Γ ++ Δ) {[]} (⊗rL (scut (⊗l-1⋆ (just (` X)) Γ {[]} axL) (⊗l⋆ (just (` X)) Γ {[]} (switch-at f))) (scut (⊗l-1⋆ nothing Δ {[]} axL) (⊗l⋆ nothing Δ {[]} g)))
    ≡⟨ cong (⊗l⋆ (just (` X)) (Γ ++ Δ)) (cong₂ ⊗rL (trans (scut⊗l-1⋆ {just (` X)}{Γ}) (cong (⊗l-1⋆ (just (` X)) Γ) (scut-axL1 _))) (trans (scut⊗l-1⋆ {nothing}{Δ}) (cong (⊗l-1⋆ nothing Δ) (scut-axL1 _)))) ⟩
      ⊗l⋆ (just (` X)) (Γ ++ Δ) {[]} (⊗rL (⊗l-1⋆ (just (` X)) Γ {[]} (⊗l⋆ (just (` X)) Γ (switch-at f))) (⊗l-1⋆ nothing Δ (⊗l⋆ nothing Δ {[]} g)))
    ≡⟨ cong (⊗l⋆ (just (` X)) (Γ ++ Δ)) (cong₂ ⊗rL (⊗l⋆-iso {just (` X)}{Γ} {f = switch-at f}) (⊗l⋆-iso {nothing}{Δ} {f = g})) ⟩
      ⊗l⋆ (just (` X)) (Γ ++ Δ) (switch-at (⊗r f g))
    ∎
  cmpltsoundR'-at {Γ} {X} (⊗r[] f g) =
    begin
      scut (⊗r[]L (switch-not Ir) axL) (⊗l (⊗rL (cmplt (soundR f)) (uf (cmplt (soundR g)))))
    ≡⟨ scut-⊗r[]L-⊗l-fma Ir axL (⊗rL (cmplt (soundR f)) (uf (cmplt (soundR g)))) ⟩
      scut axL (uf-1 (scutR Ir (⊗rL (cmplt (soundR f)) (uf (cmplt (soundR g))))))
    ≡⟨ scut-axL1 _ ⟩
      uf-1 (scutR Ir (⊗rL (cmplt (soundR f)) (uf (cmplt (soundR g)))))
    ≡⟨ cong uf-1 (cong (scutR Ir) (cong₂ ⊗rL (cmpltsoundR'-not f refl) (cong uf (cmpltsoundR'-at g) ))) ⟩
      ⊗r[]L (switch-not f) (⊗l⋆ (just (` X)) Γ (switch-at g))
    ≡⟨ ⊗r[]L⊗l⋆ {Γ} ⟩
      ⊗l⋆ (just (` X)) Γ (switch-at (⊗r[] f g))
    ∎

cmpltsound : {A B : Fma} → (f : just A ∣ [] ⊢L B) → cmplt (sound f) ≡ f
cmpltsound = cmpltsound' 

-- ====================================================================



-- strcmplt is left inverse of sound

strcmpltsound : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢L C) →
                 strcmplt (sound f) ≡ f
strcmpltsound {S}{Γ} f =
  begin
  strcmplt (sound f)
  ≡⟨ cong (⊗l-1⋆ S Γ) (cmpltsound' f) ⟩ 
  ⊗l-1⋆ S Γ (⊗l⋆ S Γ f)
  ≡⟨ ⊗l⋆-iso ⟩
  f
  ∎


