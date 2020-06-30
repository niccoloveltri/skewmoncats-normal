{-# OPTIONS --rewriting #-}

module StrongComplete where

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
open import Sound
open import Complete

{- ============================================================ -}

-- We construct a stronger completeneness map, sending a map in homset
-- ⟦ S ∣ Γ ⟧ ⇒ C to a derivation in S ∣ Γ ⊢L C.

{- ============================================================ -}

-- iterated ⊗l-1 (also applying Il-1 when appropriate)

⊗l-1⋆ : (S : Stp) → (Γ : Cxt) → {Δ : Cxt} {C : Fma} → just 〈 S ∣ Γ 〉 ∣ Δ ⊢L C → S ∣ Γ ++ Δ ⊢L C
⊗l-1⋆ (just A) [] f = f
⊗l-1⋆ (just A) (B ∷ Γ) f = ⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f)
⊗l-1⋆ nothing [] f = Il-1 f
⊗l-1⋆ nothing (B ∷ Γ) f = Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))

⊗l⋆ : (S : Stp) → (Γ : Cxt) → {Δ : Cxt}{C : Fma} → S ∣ Γ ++ Δ ⊢L C → just 〈 S ∣ Γ 〉 ∣ Δ ⊢L C
⊗l⋆ (just A) [] f = f
⊗l⋆ (just A) (B ∷ Γ) f = ⊗l⋆ (just (A ⊗ B)) Γ (⊗l f)
⊗l⋆ nothing [] f = Il f
⊗l⋆ nothing (B ∷ Γ) f = ⊗l⋆ (just (I ⊗ B)) Γ (⊗l (Il f))

-- ====================================================================

-- some lemmata

abstract
  cmplt-uf-lemma : {A B : Fma}(Γ : Cxt)(f : A ⇒ B) → cmplt [ f ∣ Γ ]f ≡ ⊗l⋆ (just A) Γ (scut (cmplt f) (⊗l-1⋆ (just B) Γ axL))
  cmplt-uf-lemma [] f = sym (scut-axL2 (cmplt f))
  cmplt-uf-lemma {A}{B} (C ∷ Γ) f = 
    begin
    cmplt [ f ⊗ id ∣ Γ ]f
    ≡⟨ cmplt-uf-lemma Γ (f ⊗ id) ⟩
    ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (⊗rL (cmplt f) (uf axL)) (⊗l-1⋆ (just (B ⊗ C)) Γ axL)))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ C)) Γ) (cong ⊗l (cong (scut (⊗rL (cmplt f) (uf axL))) (sym (⊗l⊗l-1 _)))) ⟩
    ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (⊗rL (cmplt f) (uf axL)) (⊗l (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ axL)))))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ C)) Γ) (cong ⊗l (scut-⊗rL-⊗l (cmplt f) _ _)) ⟩ 
    ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (cmplt f) (ccut [] (uf axL) (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ axL)) refl)))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ C)) Γ) (cong ⊗l (cong (scut (cmplt f)) (ccut-axL1 [] (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ axL)) refl))) ⟩
    ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (cmplt f) (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ axL))))
    ∎
  
  scut⊗l⋆ : {S : Stp}{Γ Δ Δ' : Cxt}{A C : Fma}{f : S ∣ Γ ++ Δ ⊢L A}{g : just A ∣ Δ' ⊢L C}
    → scut (⊗l⋆ S Γ {Δ} f) g ≡ ⊗l⋆ S Γ {Δ ++ Δ'} (scut f g)
  scut⊗l⋆ {just A} {[]} = refl
  scut⊗l⋆ {just A} {B ∷ Γ} = scut⊗l⋆ {just (A ⊗ B)} {Γ}
  scut⊗l⋆ {nothing} {[]} = refl
  scut⊗l⋆ {nothing} {B ∷ Γ} = scut⊗l⋆ {just (I ⊗ B)} {Γ}
  
  scut⊗l-1⋆ : {S : Stp}{Γ Δ : Cxt}{A C : Fma}{f : just 〈 S ∣ Γ 〉 ∣ [] ⊢L A}{g : just A ∣ Δ ⊢L C}
    → scut (⊗l-1⋆ S Γ f) g ≡ ⊗l-1⋆ S Γ (scut f g)
  scut⊗l-1⋆ {just A} {[]} = refl
  scut⊗l-1⋆ {just A} {B ∷ Γ}{f = f}{g} =
    begin
    scut (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f)) g
    ≡⟨ sym (scut⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f) g) ⟩
    ⊗l-1 (scut (⊗l-1⋆ (just (A ⊗ B)) Γ f) g)
    ≡⟨ cong ⊗l-1 (scut⊗l-1⋆ {just (A ⊗ B)} {Γ}) ⟩
    ⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ (scut f g))
    ∎
  scut⊗l-1⋆ {nothing} {[]} {f = f}{g} = sym (scutIl-1 f g)
  scut⊗l-1⋆ {nothing} {B ∷ Γ} {f = f}{g} =
    begin
    scut (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))) g
    ≡⟨ sym (scutIl-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)) g) ⟩
    Il-1 (scut (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)) g)
    ≡⟨ cong Il-1 (sym (scut⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f) g)) ⟩
    Il-1 (⊗l-1 (scut (⊗l-1⋆ (just (I ⊗ B)) Γ f) g))
    ≡⟨ cong Il-1 (cong ⊗l-1 (scut⊗l-1⋆ {just (I ⊗ B)} {Γ})) ⟩
    Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ (scut f g)))
    ∎
  
  ccut⊗l⋆ : {S : Stp} → {Γ' Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
           (f : nothing ∣ Γ ⊢L A) (g : S ∣ Γ' ++ Δ ⊢L C) (r : Δ ≡ Δ₀ ++ A ∷ Δ') →
           ccut Δ₀ f (⊗l⋆ S Γ' g) r ≡ ⊗l⋆ S Γ' (ccut (Γ' ++ Δ₀) f g (cong (_++_ Γ') r)  )
  ccut⊗l⋆ {just B} {[]} Δ₀ f g refl = refl
  ccut⊗l⋆ {just B} {B' ∷ Γ'} Δ₀ f g refl = ccut⊗l⋆ {just (B ⊗ B')}{Γ'} Δ₀ f (⊗l g) refl
  ccut⊗l⋆ {nothing} {[]} Δ₀ f g refl = refl
  ccut⊗l⋆ {nothing} {B ∷ Γ'} Δ₀ f g refl = ccut⊗l⋆ {just (I ⊗ B)} {Γ'} Δ₀ _ _ refl         
  
  ⊗l⋆-iso : {S : Stp}{Γ Δ : Cxt}{C : Fma}{f : S ∣ Γ ++ Δ ⊢L C} → ⊗l-1⋆ S Γ (⊗l⋆ S Γ {Δ} f) ≡ f
  ⊗l⋆-iso {just A} {[]} = refl
  ⊗l⋆-iso {just A} {B ∷ Γ} = cong ⊗l-1 (⊗l⋆-iso {just (A ⊗ B)} {Γ})
  ⊗l⋆-iso {nothing} {[]} = refl
  ⊗l⋆-iso {nothing} {B ∷ Γ} = cong Il-1 (cong ⊗l-1 (⊗l⋆-iso {just (I ⊗ B)} {Γ}))
  
  ⊗l⋆-iso2 : {S : Stp}{Γ Δ : Cxt}{C : Fma}{f : just 〈 S ∣ Γ 〉 ∣ Δ ⊢L C} → ⊗l⋆ S Γ (⊗l-1⋆ S Γ {Δ} f) ≡ f
  ⊗l⋆-iso2 {just A} {[]} = refl
  ⊗l⋆-iso2 {just A} {B ∷ Γ}{f = f}  =
    trans (cong (⊗l⋆ _ Γ) (⊗l⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f)))
      (⊗l⋆-iso2 {just (A ⊗ B)}{Γ}{_}{_}{f})
  ⊗l⋆-iso2 {nothing} {[]} = IlIl-1 _
  ⊗l⋆-iso2 {nothing} {B ∷ Γ} {f = f} =
    trans (cong (⊗l⋆ _ Γ) (cong ⊗l (IlIl-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)))))
      (trans (cong (⊗l⋆ _ Γ) (⊗l⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)))
        (⊗l⋆-iso2 {just (I ⊗ B)}{Γ}{_}{_}{f}))
  
  ⊗rL⊗l⋆ : {S : Stp}{Γ Γ' Δ : Cxt}{A B : Fma}
      → {f : S ∣ Γ ++ Γ'  ⊢L A}{g : nothing ∣ Δ ⊢L B}
      → ⊗rL (⊗l⋆ S Γ {Γ'} f) g ≡ ⊗l⋆ S Γ {Γ' ++ Δ} (⊗rL f g)
  ⊗rL⊗l⋆ {nothing} {[]} = refl
  ⊗rL⊗l⋆ {nothing} {B ∷ Γ} = ⊗rL⊗l⋆ {just (I ⊗ B)}{Γ}
  ⊗rL⊗l⋆ {just A} {[]} = refl
  ⊗rL⊗l⋆ {just A} {B ∷ Γ} = ⊗rL⊗l⋆ {just (A ⊗ B)}{Γ}

  ⊗r[]L⊗l⋆ : {Δ : Cxt}{A A' B : Fma}
      → {f : nothing ∣ []  ⊢L A}{g : just A' ∣ Δ ⊢L B}
      → ⊗r[]L f (⊗l⋆ (just A') Δ {[]} g) ≡ ⊗l⋆ (just A') Δ (⊗r[]L f g)
  ⊗r[]L⊗l⋆ {[]} = refl
  ⊗r[]L⊗l⋆ {B ∷ Δ} = ⊗r[]L⊗l⋆ {Δ}

  cmplt-⊗rL-ψ : {A B : Fma}{Δ : Cxt}
    → cmplt (ψ A B Δ) ≡ ⊗l⋆ (just (A ⊗ B)) Δ (⊗l (⊗rL axL (uf (⊗l-1⋆ (just B) Δ axL))))
  cmplt-⊗rL-ψ {Δ = []} = refl
  cmplt-⊗rL-ψ {A}{B}{C ∷ Δ} = 
    begin
    scut (cmplt [ α ∣ Δ ]f) (cmplt (ψ A (B ⊗ C) Δ))
    ≡⟨ cong (scut (cmplt [ α ∣ Δ ]f)) (cmplt-⊗rL-ψ {Δ = Δ}) ⟩ 
    scut (cmplt [ α ∣ Δ ]f) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ axL)))))
    ≡⟨ cong (λ x → scut x (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ axL)))))) (cmplt-uf-lemma Δ α) ⟩ 
    scut (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ axL))) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ axL)))))
    ≡⟨ scut⊗l⋆ {just (A ⊗ B ⊗ C)} {Δ} ⟩ 
    ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} axL)) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} axL))))))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (sym (scut-ass-scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} axL) _)) ⟩ 
    ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (scut (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} axL) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} axL)))))))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong (scut (cmplt α)) (scut⊗l-1⋆ {just (A ⊗ (B ⊗ C))}{Δ})) ⟩ 
    ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ (scut axL (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ axL)))))))) 
    ≡⟨ cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong (scut (cmplt α)) (cong (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ) (scut-axL1 _))) ⟩ 
    ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} axL)))))))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong (scut (cmplt α)) (⊗l⋆-iso {just (A ⊗ (B ⊗ C))}{Δ})) ⟩
    ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} axL)))))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong ⊗l (cong ⊗l (scut-⊗rL-⊗l axL _ _ ))) ⟩ 
    ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (⊗l (⊗l (scut axL (ccut [] (uf (⊗rL axL (uf axL))) (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ axL))) refl))))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong ⊗l (cong ⊗l (scut-axL1 _))) ⟩ 
    ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (⊗l (⊗l (ccut [] (uf (⊗rL axL (uf axL))) (⊗rL axL (uf (⊗l-1⋆ (just (B ⊗ C)) Δ axL))) refl)))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong ⊗l (cong ⊗l (ccut-⊗rL2 [] _ axL _ refl))) ⟩ 
    ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (⊗l (⊗l (⊗rL axL (uf (scut (⊗rL axL (uf axL)) (⊗l-1⋆ (just (B ⊗ C)) Δ axL))))))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong ⊗l (cong ⊗l (cong (⊗rL axL) (cong uf (sym (⊗l-1-alt (⊗l-1⋆ (just (B ⊗ C)) Δ axL))))))) ⟩ 
    ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (⊗l (⊗l (⊗rL axL (uf (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Δ axL))))))
    ∎
  
  
  ⊗l-1⋆-lem : {Γ : Cxt}{C : Fma}{f : just [ I ∣ Γ ] ∣ [] ⊢L C}
    → Il-1 (⊗l-1⋆ (just I) Γ f) ≡ ⊗l-1⋆ nothing Γ f
  ⊗l-1⋆-lem {[]} = refl
  ⊗l-1⋆-lem {B ∷ Γ} = refl
  
  ⊗l⋆-lem : {Γ : Cxt}{C : Fma}{f : nothing ∣ Γ ⊢L C}
    → ⊗l⋆ (just I) Γ {[]} (⊗rL axL f) ≡ ⊗l⋆ nothing Γ (⊗rL (switch-not Ir) f) 
  ⊗l⋆-lem {[]} = refl 
  ⊗l⋆-lem {B ∷ Γ} = refl
  
  cmplt-⊗rL-lemma : {S : Stp}{Γ Δ : Cxt}
    → cmplt (φ S Γ Δ) ≡ ⊗l⋆ S (Γ ++ Δ) (⊗rL (⊗l-1⋆ S Γ axL) (⊗l-1⋆ nothing Δ axL))
  cmplt-⊗rL-lemma {just A} {[]} {Δ}  = 
    begin
    scut (cmplt [ ρ ∣ Δ ]f) (cmplt (ψ A I Δ))
    ≡⟨ cong (λ x → scut x (cmplt (ψ A I Δ))) (cmplt-uf-lemma Δ ρ) ⟩
    scut (⊗l⋆ (just A) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (A ⊗ I)) Δ axL))) (cmplt (ψ A I Δ))
    ≡⟨ scut⊗l⋆ {just A}{Δ} ⟩
    ⊗l⋆ (just A) Δ (scut (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (A ⊗ I)) Δ axL)) (cmplt (ψ A I Δ)))
    ≡⟨ cong (⊗l⋆ (just A) Δ) (sym (scut-ass-scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (A ⊗ I)) Δ axL) _)) ⟩
    ⊗l⋆ (just A) Δ (scut (⊗rL axL (switch-not Ir)) (scut (⊗l-1⋆ (just (A ⊗ I)) Δ axL) (cmplt (ψ A I Δ))))
    ≡⟨ cong (⊗l⋆ (just A) Δ) (cong (scut (⊗rL axL (switch-not Ir))) (scut⊗l-1⋆ {just (A ⊗ I)}{Δ})) ⟩
    ⊗l⋆ (just A) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (A ⊗ I)) Δ (scut axL (cmplt (ψ A I Δ)))))
    ≡⟨ cong (⊗l⋆ (just A) Δ) (cong (scut (⊗rL axL (switch-not Ir))) (cong (⊗l-1⋆ (just (A ⊗ I)) Δ) (scut-axL1 _))) ⟩
    ⊗l⋆ (just A) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (A ⊗ I)) Δ (cmplt (ψ A I Δ))))
    ≡⟨ cong (⊗l⋆ (just A) Δ) (cong (scut (⊗rL axL (switch-not Ir))) (cong (⊗l-1⋆ (just (A ⊗ I)) Δ) (cmplt-⊗rL-ψ {A}{I}{Δ}))) ⟩
    ⊗l⋆ (just A) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (A ⊗ I)) Δ {[]} (⊗l⋆ (just (A ⊗ I)) Δ (⊗l (⊗rL axL (uf (⊗l-1⋆ (just I) Δ axL)))))))
    ≡⟨ cong (⊗l⋆ (just A) Δ) (cong (scut (⊗rL axL (switch-not Ir))) (⊗l⋆-iso {just (A ⊗ I)}{Δ})) ⟩
    ⊗l⋆ (just A) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l (⊗rL axL (uf (⊗l-1⋆ (just I) Δ axL)))))
    ≡⟨ cong (⊗l⋆ (just A) Δ) (scut-⊗rL-⊗l axL _ _) ⟩ 
    ⊗l⋆ (just A) Δ (scut axL (ccut [] (switch-not Ir) (⊗rL axL (uf (⊗l-1⋆ (just I) Δ axL))) refl))
    ≡⟨ cong (⊗l⋆ (just A) Δ) (scut-axL1 _) ⟩ 
    ⊗l⋆ (just A) Δ (ccut [] (switch-not Ir) (⊗rL axL (uf (⊗l-1⋆ (just I) Δ axL))) refl)
    ≡⟨ cong (⊗l⋆ (just A) Δ) (ccut-⊗rL2 [] _ axL _ refl) ⟩ 
    ⊗l⋆ (just A) Δ (⊗rL axL (scutR Ir (⊗l-1⋆ (just I) Δ axL)))
    ≡⟨ cong (⊗l⋆ (just A) Δ) (cong (⊗rL axL) (trans (scutR-Ir (⊗l-1⋆ (just I) Δ axL)) ⊗l-1⋆-lem)) ⟩ 
    ⊗l⋆ (just A) Δ (⊗rL axL (⊗l-1⋆ nothing Δ axL))
    ∎
  cmplt-⊗rL-lemma {just A} {B ∷ Γ} {Δ} = 
    begin
    cmplt (φ (just A) (B ∷ Γ) Δ)
    ≡⟨ cmplt-⊗rL-lemma {just (A ⊗ B)} {Γ} {Δ} ⟩
    ⊗l⋆ (just (A ⊗ B)) (Γ ++ Δ) (⊗rL (⊗l-1⋆ (just (A ⊗ B)) Γ axL) (⊗l-1⋆ nothing Δ axL))
    ≡⟨ cong (⊗l⋆ (just (A ⊗ B)) (Γ ++ Δ)) (cong₂ ⊗rL (sym (⊗l⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ axL))) refl) ⟩
    ⊗l⋆ (just (A ⊗ B)) (Γ ++ Δ) (⊗l (⊗rL (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ axL)) (⊗l-1⋆ nothing Δ axL)))
    ∎
  cmplt-⊗rL-lemma {nothing} {[]} {Δ} = 
    begin
    scut (cmplt [ ρ ∣ Δ ]f) (cmplt (ψ I I Δ))
    ≡⟨ cong (λ x → scut x (cmplt (ψ I I Δ))) (cmplt-uf-lemma Δ ρ) ⟩
    scut (⊗l⋆ (just I) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (I ⊗ I)) Δ axL))) (cmplt (ψ I I Δ))
    ≡⟨ scut⊗l⋆ {just I}{Δ} ⟩
    ⊗l⋆ (just I) Δ (scut (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (I ⊗ I)) Δ axL)) (cmplt (ψ I I Δ)))
    ≡⟨ cong (⊗l⋆ (just I) Δ) (sym (scut-ass-scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (I ⊗ I)) Δ axL) _)) ⟩
    ⊗l⋆ (just I) Δ (scut (⊗rL axL (switch-not Ir)) (scut (⊗l-1⋆ (just (I ⊗ I)) Δ axL) (cmplt (ψ I I Δ))))
    ≡⟨ cong (⊗l⋆ (just I) Δ) (cong (scut (⊗rL axL (switch-not Ir))) (scut⊗l-1⋆ {just (I ⊗ I)}{Δ})) ⟩
    ⊗l⋆ (just I) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (I ⊗ I)) Δ (scut axL (cmplt (ψ I I Δ)))))
    ≡⟨ cong (⊗l⋆ (just I) Δ) (cong (scut (⊗rL axL (switch-not Ir))) (cong (⊗l-1⋆ (just (I ⊗ I)) Δ) (scut-axL1 _))) ⟩
    ⊗l⋆ (just I) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (I ⊗ I)) Δ (cmplt (ψ I I Δ))))
    ≡⟨ cong (⊗l⋆ (just I) Δ) (cong (scut (⊗rL axL (switch-not Ir))) (cong (⊗l-1⋆ (just (I ⊗ I)) Δ) (cmplt-⊗rL-ψ {I}{I}{Δ}))) ⟩
    ⊗l⋆ (just I) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l-1⋆ (just (I ⊗ I)) Δ {[]} (⊗l⋆ (just (I ⊗ I)) Δ (⊗l (⊗rL axL (uf (⊗l-1⋆ (just I) Δ axL)))))))
    ≡⟨ cong (⊗l⋆ (just I) Δ) (cong (scut (⊗rL axL (switch-not Ir))) (⊗l⋆-iso {just (I ⊗ I)}{Δ})) ⟩
    ⊗l⋆ (just I) Δ (scut (⊗rL axL (switch-not Ir)) (⊗l (⊗rL axL (uf (⊗l-1⋆ (just I) Δ axL)))))
    ≡⟨ cong (⊗l⋆ (just I) Δ) (cong Il (trans (scutR-⊗r[]L2-not Ir (switch-not Ir) (⊗l-1⋆ (just I) Δ axL)) (cong (⊗rL (switch-not Ir)) (trans (scutR-Ir (⊗l-1⋆ (just I) Δ axL)) ⊗l-1⋆-lem)))) ⟩ 
    ⊗l⋆ (just I) Δ {[]} (⊗rL axL (⊗l-1⋆ nothing Δ axL))
    ≡⟨ ⊗l⋆-lem {Δ} ⟩
    ⊗l⋆ nothing Δ {[]} (⊗rL (switch-not Ir) (⊗l-1⋆ nothing Δ axL))
    ∎
  cmplt-⊗rL-lemma {nothing} {B ∷ Γ} {Δ} = 
    begin
    cmplt (φ nothing (B ∷ Γ) Δ)
    ≡⟨ cmplt-⊗rL-lemma {just (I ⊗ B)} {Γ} {Δ} ⟩
    ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗rL (⊗l-1⋆ (just (I ⊗ B)) Γ axL) (⊗l-1⋆ nothing Δ axL))
    ≡⟨ cong (⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ)) (cong₂ ⊗rL (sym (⊗l⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ axL))) refl) ⟩
    ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗l (⊗rL (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ axL)) (⊗l-1⋆ nothing Δ axL)))
    ≡⟨ cong (⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ)) (cong ⊗l (cong₂ ⊗rL (sym (IlIl-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ axL)))) refl)) ⟩
    ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗l (Il (⊗rL (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ axL))) (⊗l-1⋆ nothing Δ axL))))
    ∎
  
-- ====================================================================

-- The strong completeness function

strcmplt : {S : Stp}{Γ : Cxt}{C : Fma} → 〈 S ∣ Γ 〉 ⇒ C → S ∣ Γ ⊢L C
strcmplt {S}{Γ} f = ⊗l-1⋆ S Γ (cmplt f)
