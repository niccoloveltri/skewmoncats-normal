{-# OPTIONS --rewriting #-}

module StrongComplete where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk
open import Cuts
open import MulticatLaws1
open import MulticatLaws2
open import Sound
open import Complete

{- ============================================================ -}

-- We construct a stronger completeneness map, sending a map in homset
-- ⟦ S ∣ Γ ⟧ ⇒ C to a derivation in S ∣ Γ ⊢L C.

{- ============================================================ -}

-- iterated ⊗l-1 (also applying Il-1 when appropriate)

⊗l-1⋆ : (S : Stp) → (Γ : Cxt) → {Δ : Cxt} {C : Fma} → just 〈 S ∣ Γ 〉 ∣ Δ ⊢ C → S ∣ Γ ++ Δ ⊢ C
⊗l-1⋆ (just A) [] f = f
⊗l-1⋆ (just A) (B ∷ Γ) f = ⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f)
⊗l-1⋆ nothing [] f = Il-1 f
⊗l-1⋆ nothing (B ∷ Γ) f = Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))

⊗l⋆ : (S : Stp) → (Γ : Cxt) → {Δ : Cxt}{C : Fma} → S ∣ Γ ++ Δ ⊢ C → just 〈 S ∣ Γ 〉 ∣ Δ ⊢ C
⊗l⋆ (just A) [] f = f
⊗l⋆ (just A) (B ∷ Γ) f = ⊗l⋆ (just (A ⊗ B)) Γ (⊗l f)
⊗l⋆ nothing [] f = Il f
⊗l⋆ nothing (B ∷ Γ) f = ⊗l⋆ (just (I ⊗ B)) Γ (⊗l (Il f))

-- ====================================================================

-- ⊗l-1⋆ is compatible with ≗

cong⊗l-1⋆ : {S : Stp}{Γ Δ : Cxt}{C : Fma}{f g : just 〈 S ∣ Γ 〉 ∣ Δ ⊢ C} → f ≗ g → ⊗l-1⋆ S Γ {Δ} f ≗ ⊗l-1⋆ S Γ g
cong⊗l-1⋆ {just A} {[]} p = p
cong⊗l-1⋆ {just A} {B ∷ Γ} p = cong⊗l-1 (cong⊗l-1⋆ {just (A ⊗ B)} {Γ} p)
cong⊗l-1⋆ {nothing} {[]} p = congIl-1 p
cong⊗l-1⋆ {nothing} {B ∷ Γ} p = congIl-1 (cong⊗l-1 (cong⊗l-1⋆ {just (I ⊗ B)} {Γ} p))

cong⊗l⋆ : {S : Stp}{Γ Δ : Cxt}{C : Fma}{f g : S ∣ Γ ++ Δ ⊢ C} → f ≗ g → ⊗l⋆ S Γ {Δ} f ≗ ⊗l⋆ S Γ g
cong⊗l⋆ {just A} {[]} p = p
cong⊗l⋆ {just A} {B ∷ Γ} p = cong⊗l⋆ {just (A ⊗ B)} {Γ} (⊗l p)
cong⊗l⋆ {nothing} {[]} p = Il p
cong⊗l⋆ {nothing} {B ∷ Γ} p = cong⊗l⋆ {just (I ⊗ B)} {Γ} (⊗l (Il p))

-- ====================================================================

-- some lemmata

cmplt-uf-lemma : {A B : Fma}(Γ : Cxt)(f : A ⇒ B) → cmplt [ f ∣ Γ ]f ≗ ⊗l⋆ (just A) Γ (scut (cmplt f) (⊗l-1⋆ (just B) Γ ax))
cmplt-uf-lemma [] f = ~ (≡-to-≗ (scut-unit (cmplt f)))
cmplt-uf-lemma {A}{B} (C ∷ Γ) f =
  proof≗
  cmplt [ f ⊗ id ∣ Γ ]f
  ≗〈 cmplt-uf-lemma Γ (f ⊗ id) 〉
  ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (⊗r (cmplt f) (uf ax)) (⊗l-1⋆ (just (B ⊗ C)) Γ ax)))
  ≗〈 cong⊗l⋆ (⊗l (cong-scut {f = ⊗r (cmplt f) (uf ax)}  refl (~ (⊗l⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ ax))))) 〉
  ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (⊗r (cmplt f) (uf ax)) (⊗l (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ ax)))))
  ≗〈 cong⊗l⋆ {just (A ⊗ C)} {Γ} (⊗l (cong-scut {f = cmplt f} refl (≡-to-≗ (ccut-unit [] _ refl)))) 〉
  ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (cmplt f) (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ ax))))
  qed≗

scut⊗l⋆ : {S : Stp}{Γ Δ Δ' : Cxt}{A C : Fma}{f : S ∣ Γ ++ Δ ⊢ A}{g : just A ∣ Δ' ⊢ C}
  → scut (⊗l⋆ S Γ {Δ} f) g ≡ ⊗l⋆ S Γ {Δ ++ Δ'} (scut f g)
scut⊗l⋆ {just A} {[]} = refl
scut⊗l⋆ {just A} {B ∷ Γ} = scut⊗l⋆ {just (A ⊗ B)} {Γ}
scut⊗l⋆ {nothing} {[]} = refl
scut⊗l⋆ {nothing} {B ∷ Γ} = scut⊗l⋆ {just (I ⊗ B)} {Γ}

scut⊗l-1⋆ : {S : Stp}{Γ Δ : Cxt}{A C : Fma}{f : just 〈 S ∣ Γ 〉 ∣ [] ⊢ A}{g : just A ∣ Δ ⊢ C}
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

ccut⊗l⋆ : (b : Bool) {S : Stp} → {Γ' Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
         (f : nothing ∣ Γ ⊢ A) (g : S ∣ Γ' ++ Δ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ') →
         ccut b Δ₀ f (⊗l⋆ S Γ' g) r ≡ ⊗l⋆ S Γ' (ccut b (Γ' ++ Δ₀) f g (cong (_++_ Γ') r)  )
ccut⊗l⋆ b {just B} {[]} Δ₀ f g refl = refl
ccut⊗l⋆ b {just B} {B' ∷ Γ'} Δ₀ f g refl = ccut⊗l⋆ b {just (B ⊗ B')}{Γ'} Δ₀ f (⊗l g) refl
ccut⊗l⋆ b {nothing} {[]} Δ₀ f g refl = refl
ccut⊗l⋆ b {nothing} {B ∷ Γ'} Δ₀ f g refl = ccut⊗l⋆ b {just (I ⊗ B)} {Γ'} Δ₀ _ _ refl         

⊗l⋆-iso : {S : Stp}{Γ Δ : Cxt}{C : Fma}{f : S ∣ Γ ++ Δ ⊢ C} → ⊗l-1⋆ S Γ (⊗l⋆ S Γ {Δ} f) ≡ f
⊗l⋆-iso {just A} {[]} = refl
⊗l⋆-iso {just A} {B ∷ Γ} = cong ⊗l-1 (⊗l⋆-iso {just (A ⊗ B)} {Γ})
⊗l⋆-iso {nothing} {[]} = refl
⊗l⋆-iso {nothing} {B ∷ Γ} = cong Il-1 (cong ⊗l-1 (⊗l⋆-iso {just (I ⊗ B)} {Γ}))

⊗l⋆-iso2 : {S : Stp}{Γ Δ : Cxt}{C : Fma}{f : just 〈 S ∣ Γ 〉 ∣ Δ ⊢ C} → ⊗l⋆ S Γ (⊗l-1⋆ S Γ {Δ} f) ≗ f
⊗l⋆-iso2 {just A} {[]} = refl
⊗l⋆-iso2 {just A} {B ∷ Γ}{f = f}  = (cong⊗l⋆ {_}{Γ} (⊗l⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f))) ∙ (⊗l⋆-iso2 {just (A ⊗ B)}{Γ}{_}{_}{f})
⊗l⋆-iso2 {nothing} {[]} = IlIl-1 _
⊗l⋆-iso2 {nothing} {B ∷ Γ} {f = f} =
  cong⊗l⋆ {_}{Γ} (⊗l (IlIl-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))))
  ∙ cong⊗l⋆ {_}{Γ} (⊗l⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))
  ∙ ⊗l⋆-iso2 {just (I ⊗ B)}{Γ}{_}{_}{f}

⊗r⊗l⋆ : {S : Stp}{Γ Γ' Δ : Cxt}{A B : Fma}
    → {f : S ∣ Γ ++ Γ'  ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗l⋆ S Γ {Γ'} f) g ≗ ⊗l⋆ S Γ {Γ' ++ Δ} (⊗r f g)
⊗r⊗l⋆ {just A} {[]} = refl
⊗r⊗l⋆ {just A} {B ∷ Γ}{_}{Δ}{C}{D}{f}{g} =
  proof≗
  ⊗r (⊗l⋆ (just (A ⊗ B)) Γ (⊗l f)) g
  ≗〈 ⊗r⊗l⋆ {just (A ⊗ B)}{Γ} 〉 
  ⊗l⋆ (just (A ⊗ B)) Γ (⊗r (⊗l f) g)
  ≗〈 cong⊗l⋆ {just (A ⊗ B)} {Γ} ⊗r⊗l 〉 
  ⊗l⋆ (just (A ⊗ B)) Γ (⊗l (⊗r f g))
  qed≗
⊗r⊗l⋆ {nothing} {[]} = ⊗rIl
⊗r⊗l⋆ {nothing} {B ∷ Γ}{_}{Δ}{C}{D}{f}{g} =
  proof≗
  ⊗r (⊗l⋆ (just (I ⊗ B)) Γ (⊗l (Il f))) g
  ≗〈 ⊗r⊗l⋆ {just (I ⊗ B)}{Γ} 〉 
  ⊗l⋆ (just (I ⊗ B)) Γ (⊗r (⊗l (Il f)) g)
  ≗〈 cong⊗l⋆ {just (I ⊗ B)} {Γ} ⊗r⊗l 〉 
  ⊗l⋆ (just (I ⊗ B)) Γ (⊗l (⊗r (Il f) g))
  ≗〈 cong⊗l⋆ {just (I ⊗ B)} {Γ} (⊗l ⊗rIl) 〉 
  ⊗l⋆ (just (I ⊗ B)) Γ (⊗l (Il (⊗r f g)))
  qed≗

cmplt-⊗r-ψ : {A B : Fma}{Δ : Cxt}
  → cmplt (ψ A B Δ) ≗ ⊗l⋆ (just (A ⊗ B)) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just B) Δ ax))))
cmplt-⊗r-ψ {Δ = []} = ax⊗
cmplt-⊗r-ψ {A}{B}{C ∷ Δ}  =
  proof≗
  scut (cmplt [ α ∣ Δ ]f) (cmplt (ψ A (B ⊗ C) Δ))
  ≗〈 cong-scut {f = cmplt [ α ∣ Δ ]f} refl (cmplt-⊗r-ψ {Δ = Δ}) 〉 
  scut (cmplt [ α ∣ Δ ]f) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ ax)))))
  ≗〈 cong-scut (cmplt-uf-lemma Δ α) refl 〉 
  scut (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ ax))) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ ax)))))
  ≗〈 ≡-to-≗ (scut⊗l⋆ {just (A ⊗ B ⊗ C)} {Δ}) 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} ax)) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax))))))
  ≗〈 cong⊗l⋆ {just (A ⊗ B ⊗ C)} {Δ} (~ (scut-ass-scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} ax) _)) 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (scut (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} ax) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax)))))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong (scut (cmplt α)) (scut⊗l-1⋆ {just (A ⊗ (B ⊗ C))}{Δ}))) 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ (scut ax (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax))))))))
  ≗〈 refl 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax)))))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong (scut (cmplt α)) (⊗l⋆-iso {just (A ⊗ (B ⊗ C))}{Δ}))) 〉
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax)))))
  ≗〈 refl 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (⊗l (⊗l (⊗r ax (uf (scut (⊗r ax (uf ax)) (⊗l-1⋆ (just (B ⊗ C)) Δ ax))))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong ⊗l (cong ⊗l (cong (⊗r ax) (cong uf (sym (⊗l-1-alt (⊗l-1⋆ (just (B ⊗ C)) Δ ax)))))))) 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (⊗l (⊗l (⊗r ax (uf (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Δ ax))))))
  qed≗

⊗l-1⋆-lem : {Γ : Cxt}{C : Fma}{f : just [ I ∣ Γ ] ∣ [] ⊢ C}
  → Il-1 (⊗l-1⋆ (just I) Γ f) ≡ ⊗l-1⋆ nothing Γ f
⊗l-1⋆-lem {[]} = refl
⊗l-1⋆-lem {B ∷ Γ} = refl

⊗l⋆-lem : {Γ : Cxt}{C : Fma}{f : nothing ∣ Γ ⊢ C}
  → ⊗l⋆ (just I) Γ {[]} (⊗r ax f) ≗ ⊗l⋆ nothing Γ (⊗r Ir f)
⊗l⋆-lem {[]} = ⊗r axI refl ∙ ⊗rIl
⊗l⋆-lem {B ∷ Γ} = cong⊗l⋆ {just (I ⊗ B)} {Γ} (⊗l (⊗r axI refl ∙ ⊗rIl))

cmplt-⊗r-lemma : {S : Stp}{Γ Δ : Cxt}
  → cmplt (φ S Γ Δ) ≗ ⊗l⋆ S (Γ ++ Δ) (⊗r (⊗l-1⋆ S Γ ax) (⊗l-1⋆ nothing Δ ax))
cmplt-⊗r-lemma {just A} {[]} {Δ}  =
  proof≗
  scut (cmplt [ ρ ∣ Δ ]f) (cmplt (ψ A I Δ))
  ≗〈 cong-scut (cmplt-uf-lemma Δ ρ) refl 〉
  scut (⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ ax))) (cmplt (ψ A I Δ))
  ≗〈 ≡-to-≗ (scut⊗l⋆ {just A}{Δ}) 〉
  ⊗l⋆ (just A) Δ (scut (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ ax)) (cmplt (ψ A I Δ)))
  ≗〈 cong⊗l⋆ {just A}{Δ} (~ (scut-ass-scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ ax) _)) 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (scut (⊗l-1⋆ (just (A ⊗ I)) Δ ax) (cmplt (ψ A I Δ))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just A) Δ) (cong (scut (⊗r ax Ir)) (scut⊗l-1⋆ {just (A ⊗ I)}{Δ}))) 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ (scut ax (cmplt (ψ A I Δ)))))
  ≗〈 refl 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ (cmplt (ψ A I Δ))))
  ≗〈 cong⊗l⋆ {just A} {Δ} (cong-scut {f = ⊗r ax Ir} refl (cong⊗l-1⋆ {just (A ⊗ I)} {Δ} (cmplt-⊗r-ψ {A}{I}{Δ}))) 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ {[]} (⊗l⋆ (just (A ⊗ I)) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just I) Δ ax)))))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just A) Δ) (cong (scut (⊗r ax Ir)) (⊗l⋆-iso {just (A ⊗ I)}{Δ}))) 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l (⊗r ax (uf (⊗l-1⋆ (just I) Δ ax)))))
  ≗〈 cong⊗l⋆ {just A} {Δ} (⊗r refl ((~ (≡-to-≗ (Il-1-scutIr (⊗l-1⋆ (just I) Δ ax)))) ∙ ≡-to-≗ (⊗l-1⋆-lem {Δ}))) 〉
  ⊗l⋆ (just A) Δ (⊗r ax (⊗l-1⋆ nothing Δ ax))
  qed≗
cmplt-⊗r-lemma {just A} {B ∷ Γ} {Δ} =
  proof≗
  cmplt (φ (just A) (B ∷ Γ) Δ)
  ≗〈 cmplt-⊗r-lemma {just (A ⊗ B)} {Γ} {Δ} 〉
  ⊗l⋆ (just (A ⊗ B)) (Γ ++ Δ) (⊗r (⊗l-1⋆ (just (A ⊗ B)) Γ ax) (⊗l-1⋆ nothing Δ ax))
  ≗〈 cong⊗l⋆ {just (A ⊗ B)} {Γ ++ Δ} (⊗r (~ (⊗l⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ ax) )) refl) 〉
  ⊗l⋆ (just (A ⊗ B)) (Γ ++ Δ) (⊗r (⊗l (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ ax))) (⊗l-1⋆ nothing Δ ax))
  ≗〈 cong⊗l⋆ {just (A ⊗ B)} {Γ ++ Δ} ⊗r⊗l 〉
  ⊗l⋆ (just (A ⊗ B)) (Γ ++ Δ) (⊗l (⊗r (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ ax)) (⊗l-1⋆ nothing Δ ax)))
  qed≗
cmplt-⊗r-lemma {nothing} {[]} {Δ} =
  proof≗
  scut (cmplt [ ρ ∣ Δ ]f) (cmplt (ψ I I Δ))
  ≗〈 cong-scut (cmplt-uf-lemma Δ ρ) refl 〉
  scut (⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ ax))) (cmplt (ψ I I Δ))
  ≗〈 ≡-to-≗ (scut⊗l⋆ {just I}{Δ}) 〉
  ⊗l⋆ (just I) Δ (scut (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ ax)) (cmplt (ψ I I Δ)))
  ≗〈 cong⊗l⋆ {just I}{Δ} (~ (scut-ass-scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ ax) _)) 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (scut (⊗l-1⋆ (just (I ⊗ I)) Δ ax) (cmplt (ψ I I Δ))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just I) Δ) (cong (scut (⊗r ax Ir)) (scut⊗l-1⋆ {just (I ⊗ I)}{Δ}))) 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ (scut ax (cmplt (ψ I I Δ)))))
  ≗〈 refl 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ (cmplt (ψ I I Δ))))
  ≗〈 cong⊗l⋆ {just I} {Δ} {[]} (cong-scut {f = ⊗r ax Ir} refl (cong⊗l-1⋆ {just (I ⊗ I)} {Δ} (cmplt-⊗r-ψ {I}{I}{Δ}))) 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ {[]} (⊗l⋆ (just (I ⊗ I)) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just I) Δ ax)))))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just I) Δ) (cong (scut (⊗r ax Ir)) (⊗l⋆-iso {just (I ⊗ I)}{Δ}))) 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l (⊗r ax (uf (⊗l-1⋆ (just I) Δ ax)))))
  ≗〈 cong⊗l⋆ {just I} {Δ} (⊗r refl ((~ (≡-to-≗ (Il-1-scutIr ((⊗l-1⋆ (just I) Δ ax))))) ∙ ≡-to-≗ (⊗l-1⋆-lem {Δ}))) 〉
  ⊗l⋆ (just I) Δ {[]} (⊗r ax (⊗l-1⋆ nothing Δ ax))
  ≗〈 ⊗l⋆-lem {Δ} 〉
  ⊗l⋆ nothing Δ {[]} (⊗r Ir (⊗l-1⋆ nothing Δ ax))
  qed≗
cmplt-⊗r-lemma {nothing} {B ∷ Γ} {Δ} = 
  proof≗
  cmplt (φ nothing (B ∷ Γ) Δ)
  ≗〈 cmplt-⊗r-lemma {just (I ⊗ B)} {Γ} {Δ} 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗r (⊗l-1⋆ (just (I ⊗ B)) Γ ax) (⊗l-1⋆ nothing Δ ax))
  ≗〈 cong⊗l⋆ {just (I ⊗ B)} {Γ ++ Δ} (⊗r (~ (⊗l⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax) )) refl) 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗r (⊗l (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax))) (⊗l-1⋆ nothing Δ ax))
  ≗〈 cong⊗l⋆ {just (I ⊗ B)} {Γ ++ Δ} ⊗r⊗l 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗l (⊗r (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax)) (⊗l-1⋆ nothing Δ ax)))
  ≗〈 cong⊗l⋆ {just (I ⊗ B)} {Γ ++ Δ} (⊗l (⊗r (~ (IlIl-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax)))) refl)) 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗l (⊗r (Il (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax)))) (⊗l-1⋆ nothing Δ ax)))
  ≗〈 cong⊗l⋆ {just (I ⊗ B)} {Γ ++ Δ} (⊗l ⊗rIl) 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗l (Il (⊗r (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax))) (⊗l-1⋆ nothing Δ ax))))
  qed≗
  
ccut-lem : (b : Bool) {S : Stp}{Γ Δ : Cxt}{A B C : Fma}
  → {f : nothing ∣ Γ ⊢ A}{g : S ∣ Δ ⊢ B}{h : nothing ∣ A ∷ [] ⊢ C}
  → ccut b Δ f (⊗r g h) refl ≡ ⊗r g (ccut b [] f h refl)
ccut-lem b {Δ = Δ}{A = A} with cases++ Δ Δ [] (A ∷ []) refl
ccut-lem b {Δ = Δ} {A} | inj₁ (Δ₀ , p , q) = ⊥-elim ([]disj∷ Δ₀ q)
ccut-lem b {Δ = Δ} {A} | inj₂ (Δ₀ , p , q) with canc++ [] Δ₀ {A ∷ []} p
ccut-lem b {Δ = Δ} {A} | inj₂ (.[] , refl , refl) | refl = refl




-- ====================================================================

-- The strong completeness function

strcmplt : {S : Stp}{Γ : Cxt}{C : Fma} → 〈 S ∣ Γ 〉 ⇒ C → S ∣ Γ ⊢ C
strcmplt {S}{Γ} f = ⊗l-1⋆ S Γ (cmplt f)
