{-# OPTIONS --rewriting #-}

module MulticatLaws where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk

-- more laws satisfied by the cut rules (associativity, parallel
-- composition)

abstract
  mutual
    scut-par-ccut : {T : Stp}{Γ₁ Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₂ C : Fma}
      → (f₁ : T ∣ Γ₁ ⊢L A₁)(f₂ : nothing ∣ Γ₂ ⊢L A₂)(g : just A₁ ∣ Δ ⊢L C)
      → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
      → scut f₁ (ccut Δ₀ f₂ g r) ≡ ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_++_ Γ₁) r)
    scut-par-ccut Δ₀ (uf f₁) f₂ g refl = cong uf (scut-par-ccut Δ₀ f₁ f₂ g refl)
    scut-par-ccut Δ₀ (Il f₁) f₂ g r = cong Il (scut-par-ccut Δ₀ f₁ f₂ g r)
    scut-par-ccut Δ₀ (⊗l f₁) f₂ g refl = cong ⊗l (scut-par-ccut Δ₀ f₁ f₂ g refl)
    scut-par-ccut Δ₀ (switch-at f₁) f₂ g r = scutR-par-ccut Δ₀ f₁ f₂ g r
    scut-par-ccut Δ₀ (switch-not f₁) f₂ g r = scutR-par-ccut Δ₀ f₁ f₂ g r

    scutR-par-ccut : {T : StpR}{Γ₁ Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₂ C : Fma}
      → (f₁ : T ∣ Γ₁ ⊢R A₁)(f₂ : nothing ∣ Γ₂ ⊢L A₂)(g : just A₁ ∣ Δ ⊢L C)
      → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
      → scutR f₁ (ccut Δ₀ f₂ g r) ≡ ccut (Γ₁ ++ Δ₀) f₂ (scutR f₁ g) (cong (_++_ Γ₁) r)
    scutR-par-ccut Δ₀ ax f₂ g refl = refl
    scutR-par-ccut Δ₀ Ir f₂ (Il g) refl = refl
    scutR-par-ccut Δ₀ (⊗r {Δ = Δ} f₁ f₁') f₂ (⊗l g) refl =
      trans (cong (scutR f₁) (ccut-par-ccut [] f₁' f₂ g refl))
        (scutR-par-ccut (Δ ++ Δ₀) f₁ f₂ (ccut [] f₁' g refl) refl)
    scutR-par-ccut Δ₀ (⊗r[] f₁ f₁') f₂ (⊗l g) refl =
      trans
        (cong (scutR f₁')
          (trans
            (cong uf-1 (scutR-par-ccut (_ ∷ Δ₀) f₁ f₂ g refl))
            (sym (ccut-uf-1' Δ₀ f₂ (scutR f₁ g) refl))))
        (scutR-par-ccut Δ₀ f₁' f₂ (uf-1' (scutR f₁ g) refl) refl)

    ccut-par-ccut : {T : Stp} → {Γ₁ Γ₂ : Cxt} → (Δ₀ : Cxt) → {Δ Δ₁ Δ₂ : Cxt} → {A₁ A₂ C : Fma}
      → (f₁ : nothing ∣ Γ₁ ⊢L A₁)(f₂ : nothing ∣ Γ₂ ⊢L A₂)(g : T ∣ Δ ⊢L C)
      → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
     → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) refl ≡ ccut (Δ₀ ++ Γ₁ ++ Δ₁) f₂ (ccut Δ₀ f₁ g r) refl
    ccut-par-ccut Δ₀ f₁ f₂ (uf g) r with cases∷ Δ₀ r
    ccut-par-ccut .[] {Δ₁ = Δ₁} f₁ f₂ (uf g) refl | inj₁ (refl , refl , refl) = scut-par-ccut Δ₁ f₁ f₂ g refl
    ccut-par-ccut .(_ ∷ Γ₀) f₁ f₂ (uf g) refl | inj₂ (Γ₀ , refl , refl) = cong uf (ccut-par-ccut Γ₀ f₁ f₂ g refl)
    ccut-par-ccut Δ₀ f₁ f₂ (Il g) r = cong Il (ccut-par-ccut Δ₀ f₁ f₂ g r)
    ccut-par-ccut Δ₀ f₁ f₂ (⊗l g) refl = cong ⊗l (ccut-par-ccut (_ ∷ Δ₀) f₁ f₂ g refl)
    ccut-par-ccut Δ₀ f₁ f₂ (switch-at g) refl =
      cong switch-at (ccutR-par-ccutR Δ₀ f₁ f₂ g refl)
    ccut-par-ccut Δ₀ f₁ f₂ (switch-not g) r = ⊥-elim ([]disj∷ Δ₀ r) 

    ccutR-par-ccutR : {T : StpR} → {Γ₁ Γ₂ : Cxt} → (Δ₀ : Cxt) → {Δ Δ₁ Δ₂ : Cxt} → {A₁ A₂ C : Fma}
      → (f₁ : nothing ∣ Γ₁ ⊢L A₁)(f₂ : nothing ∣ Γ₂ ⊢L A₂)(g : T ∣ Δ ⊢R C)
      → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
     → ccutR Δ₀ f₁ (ccutR (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) refl ≡ ccutR (Δ₀ ++ Γ₁ ++ Δ₁) f₂ (ccutR Δ₀ f₁ g r) refl
    ccutR-par-ccutR Δ₀ f₁ f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
    ccutR-par-ccutR Δ₀ f₁ f₂ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
    ccutR-par-ccutR Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} {Δ} g g') r with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ Δ r
    ccutR-par-ccutR {Γ₁ = Γ₁}{Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀ ++ Δ)} {A₁} {A₂} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl)
      rewrite cases++-inj₁ Δ₀ (Δ₁ ++ Γ₂ ++ Γ₀) Δ A₁ | cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) Δ A₁ | cases++-inj₁ (Δ₀ ++ Γ₁ ++ Δ₁) Γ₀ Δ A₂ =
      cong₂ (⊗r {Γ = Δ₀ ++ Γ₁ ++ Δ₁ ++ Γ₂ ++ Γ₀}{Δ}) (ccutR-par-ccutR Δ₀ f₁ f₂ g refl) refl 
    ccutR-par-ccutR Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} {.(Γ₀ ++ A₂ ∷ Δ₂)} g g') r | inj₂ (Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym q)
    ccutR-par-ccutR {Γ₁ = Γ₁}{Γ₂} Δ₀ {Δ₁ = .(Γ₀' ++ Γ₀)} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₁ ∷ Γ₀')} {.(Γ₀ ++ A₂ ∷ Δ₂)} g g') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) 
      rewrite cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ Γ₂ ++ Δ₂) A₁ | cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ Γ₀ (Δ₀ ++ Γ₁ ++ Γ₀') Δ₂ A₂ = refl
    ccutR-par-ccutR {Γ₁ = Γ₁}{Γ₂} .(Γ ++ Γ₀') {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g') refl | inj₂ (._ , refl , refl) | inj₂ (Γ₀' , refl , refl)
      rewrite cases++-inj₂ Γ₀' Γ (Δ₁ ++ Γ₂ ++ Δ₂) A₁ | cases++-inj₂ Γ₀' Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (Γ₀' ++ Γ₁ ++ Δ₁) Γ Δ₂ A₂ =
      cong (⊗r g) (ccut-par-ccut Γ₀' f₁ f₂ g' refl)
    ccutR-par-ccutR Δ₀ f₁ f₂ (⊗r[] g g') r = cong (⊗r[] g) (ccutR-par-ccutR Δ₀ f₁ f₂ g' r)     


  scutR-ccut-eq : {Γ Γ' Δ : Cxt} → {Δ' : Cxt} → {A₁ A₂ C : Fma}
      → (f₁ : nothing ∣ Γ' ⊢R A₁)(f₂ : nothing ∣ Γ ⊢L A₂)(g : just A₁ ∣ Δ ⊢L C)
      → (r : Δ ≡ A₂ ∷ Δ') (r' : Γ' ≡ [])
      → scutR (subst-cxtR r' f₁) (ccut [] f₂ g r) ≡ scut f₂ (uf-1' (scutR (subst-cxtR r' f₁) g) r) 
  scutR-ccut-eq Ir f₂ (Il (uf g)) refl refl = refl
  scutR-ccut-eq (⊗r {Γ = []} f₁ f₁') f₂ (⊗l g) refl refl =
    trans
      (cong (scutR f₁) (ccut-par-ccut [] f₁' f₂ g refl))
      (scutR-ccut-eq f₁ f₂ (ccut [] f₁' g refl) refl refl)

  mutual
    scut-⊗r[]L-⊗l-not : {Γ Δ : Cxt} → {A B C : Fma}
      → (f : nothing ∣ [] ⊢R A) (f' : nothing ∣ Γ ⊢L B)  (g : just A ∣ B ∷  Δ ⊢L C)
      →  scut (⊗rL (switch-not f) f') (⊗l g) ≡ scut f' (uf-1 (scutR f g)) 
    scut-⊗r[]L-⊗l-not f (uf f') g = cong uf (scut-⊗r[]L-⊗l-fma f f' g)
    scut-⊗r[]L-⊗l-not f (switch-not f₁) g = scutR-ccut-eq f (switch-not f₁) g refl refl
  
    scut-⊗r[]L-⊗l-fma : {Γ Δ : Cxt} → {A A' B C : Fma}
      → (f : nothing ∣ [] ⊢R A) (f' : just A' ∣ Γ ⊢L B)  (g : just A ∣ B ∷  Δ ⊢L C)
      →  scut (⊗r[]L (switch-not f) f') (⊗l g) ≡ scut f' (uf-1 (scutR f g)) 
    scut-⊗r[]L-⊗l-fma f (Il f') g = cong Il (scut-⊗r[]L-⊗l-not f f' g)
    scut-⊗r[]L-⊗l-fma f (⊗l f') g = cong ⊗l (scut-⊗r[]L-⊗l-fma f f' g)
    scut-⊗r[]L-⊗l-fma f (switch-at f₁) g = refl

  scut-⊗rL-⊗l : {S : Stp} {Γ Γ' Δ : Cxt} → {A B C : Fma}
    → (f : S ∣ Γ ⊢L A) (f' : nothing ∣ Γ' ⊢L B)  (g : just A ∣ B ∷  Δ ⊢L C)
    →  scut (⊗rL f f') (⊗l g) ≡ scut f (ccut [] f' g refl)
  scut-⊗rL-⊗l (uf f) f' g = cong uf (scut-⊗rL-⊗l f f' g)
  scut-⊗rL-⊗l (Il f) f' g = cong Il (scut-⊗rL-⊗l f f' g)
  scut-⊗rL-⊗l (⊗l f) f' g = cong ⊗l (scut-⊗rL-⊗l f f' g)
  scut-⊗rL-⊗l (switch-at f) f' g = refl
  scut-⊗rL-⊗l (switch-not f) (uf f') g = 
    trans (cong uf (scut-⊗r[]L-⊗l-fma f f' g)) (sym (scutR-ccut-eq f (uf f') g refl refl))
  scut-⊗rL-⊗l (switch-not f) (switch-not f') g = refl

  mutual
    ccut-axL1 : {T : Stp} {Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma} → 
                (g : T ∣ Δ ⊢L C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
                  ccut Δ₀ (uf axL) g r ≡ subst-cxt r g
    ccut-axL1 Δ₀ (uf g) r with cases∷ Δ₀ r
    ccut-axL1 .[] (uf g) refl | inj₁ (refl , refl , refl) =
      cong uf (scut-axL1 g)
    ccut-axL1 .(_ ∷ Γ₀) (uf g) refl | inj₂ (Γ₀ , refl , refl) =
      cong uf (ccut-axL1  Γ₀ g refl)
    ccut-axL1 Δ₀ (Il g) refl = cong Il (ccut-axL1 Δ₀ g refl)
    ccut-axL1 Δ₀ (⊗l g) refl = cong ⊗l (ccut-axL1 (_ ∷ Δ₀) g refl)
    ccut-axL1 Δ₀ (switch-at g) refl = cong switch-at (ccutR-axL1 Δ₀ g refl)  
    ccut-axL1 Δ₀ (switch-not g) r = ⊥-elim ([]disj∷ Δ₀ r)
  
    ccutR-axL1 : {T : StpR} {Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma} → 
               (g : T ∣ Δ ⊢R C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
                 ccutR Δ₀ (uf axL) g r ≡ subst-cxtR r g
    ccutR-axL1 Δ₀ ax r = ⊥-elim ([]disj∷ Δ₀ r)
    ccutR-axL1 Δ₀ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
    ccutR-axL1 Δ₀ {Δ'} (⊗r {Γ = Γ} {Δ} g g') r with cases++ Δ₀ Γ Δ' Δ r
    ccutR-axL1 Δ₀ {.(Γ₀ ++ Δ)} (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) = cong₂ (⊗r {Γ = Δ₀ ++ _ ∷ Γ₀}{Δ}) (ccutR-axL1 Δ₀ g refl) refl
    ccutR-axL1 .(Γ ++ Γ₀) {Δ'} (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) = cong (⊗r g) (ccut-axL1 Γ₀ g' refl)
    ccutR-axL1 Δ₀ (⊗r[] g g') refl = cong (⊗r[] g) (ccutR-axL1 Δ₀ g' refl)
    
    scut-axL1 : {Δ : Cxt} → {A C : Fma}
      → (g : just A ∣ Δ ⊢L C)
      →  scut axL g ≡ g
    scut-axL1 {A = ` X} g = refl
    scut-axL1 {A = I} (Il g) = refl
    scut-axL1 {A = A ⊗ B} (⊗l g) =
      cong ⊗l
        (trans (scut-⊗rL-⊗l axL (uf axL) g)
          (trans (scut-axL1 _) (ccut-axL1 [] g refl)))

  mutual
    scut-axL2 : {S : Stp} {Γ : Cxt} → {A : Fma}
      → (f : S ∣ Γ ⊢L A)
      →  scut f axL ≡ f
    scut-axL2 (uf f) = cong uf (scut-axL2 f)
    scut-axL2 (Il f) = cong Il (scut-axL2 f)
    scut-axL2 (⊗l f) = cong ⊗l (scut-axL2 f)
    scut-axL2 (switch-at f) = scutR-axL2-at f
    scut-axL2 (switch-not f) = scutR-axL2-not f refl

    scutR-axL2-at : {Γ : Cxt} → {X : At} {A : Fma}
      → (f : just X ∣ Γ ⊢R A)
      →  scutR f axL ≡ switch-at f
    scutR-axL2-at ax = refl
    scutR-axL2-at (⊗r f g) =
      trans (cong (scutR f) (ccut-⊗rL2 [] g axL (uf axL) refl))
        (trans (cong (scutR f) (cong (⊗rL axL) (scut-axL2 g)))
          (trans (scutR-⊗rL2 f axL g)
            (cong₂ ⊗rL (scutR-axL2-at f) refl)))
    scutR-axL2-at (⊗r[] f g) =
      trans (cong (scutR g) (cong uf-1 (trans (scutR-⊗rL2 f axL (uf axL)) (cong₂ ⊗rL (scutR-axL2-not f refl) refl))))
        (trans (scutR-⊗r[]L2-fma g (switch-not f) axL)
          (cong (⊗r[]L (switch-not f)) (scutR-axL2-at g)))

    scutR-axL2-not : {Γ : Cxt} → {A : Fma}
      → (f : nothing ∣ Γ ⊢R A) (r : Γ ≡ [])
      →  scutR (subst-cxtR r f) axL ≡ switch-not (subst-cxtR r f)
    scutR-axL2-not Ir refl = refl
    scutR-axL2-not (⊗r {Γ = []} f (switch-not g)) refl =
      trans (scutR-par-ccut [] f (switch-not g) (⊗rL axL (uf axL)) refl)
        (trans (cong (λ x → ccut [] (switch-not g) x refl) (trans (scutR-⊗rL2 f axL (uf axL)) (cong₂ ⊗rL (scutR-axL2-not f refl) refl)))
          (trans (scut-⊗r[]L2-not (switch-not g) (switch-not f) axL)
            (cong (⊗rL (switch-not f)) (scutR-axL2-not g refl) )))
    

-- ====================================================================

  mutual
    scut-ass-scut : {S : Stp} → {Γ Δ Δ' : Cxt} → {A B C : Fma}
      → (f : S ∣ Γ ⊢L A)(g : just A ∣ Δ ⊢L B)(h : just B ∣ Δ' ⊢L C)
      → scut f (scut g h) ≡ scut (scut f g) h
    scut-ass-scut (uf f) g h = cong uf (scut-ass-scut f g h)
    scut-ass-scut (Il f) g h = cong Il (scut-ass-scut f g h)
    scut-ass-scut (⊗l f) g h = cong ⊗l (scut-ass-scut f g h)
    scut-ass-scut (switch-at f) g h = scutR-ass-scut f g h
    scut-ass-scut (switch-not f) g h = scutR-ass-scut f g h 

    scutR-ass-scut : {S : StpR} → {Γ Δ Δ' : Cxt} → {A B C : Fma}
      → (f : S ∣ Γ ⊢R A)(g : just A ∣ Δ ⊢L B)(h : just B ∣ Δ' ⊢L C)
      → scutR f (scut g h) ≡ scut (scutR f g) h
    scutR-ass-scut ax g h = refl
    scutR-ass-scut Ir (Il g) h = refl
    scutR-ass-scut (⊗r f f') (⊗l g) h =
      trans (cong (scutR f) (ccut-ass-scut [] f' g h refl))
        (scutR-ass-scut f (ccut [] f' g refl) h)
    scutR-ass-scut (⊗r[] f f') (⊗l g) h =
      trans
        (cong (scutR f')
            (trans
              (cong uf-1 (scutR-ass-scut f g h))
              (sym (scut-uf-1' (scutR f g) h refl))))
        (scutR-ass-scut  f' (uf-1 (scutR f g)) h)

    ccut-ass-scut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A B C : Fma}
      → (f : nothing ∣ Γ ⊢L A)(g : T ∣ Δ ⊢L B)(h : just B ∣ Δ'' ⊢L C)
      → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
      → ccut Δ₀ f (scut g h) (cong₂ _++_ r (refl {x = Δ''})) ≡ scut (ccut Δ₀ f g r) h
    ccut-ass-scut Δ₀ f (uf g) h r with cases∷ Δ₀ r
    ccut-ass-scut .[] f (uf g) h refl | inj₁ (refl , refl , refl) = scut-ass-scut f g h
    ccut-ass-scut .(_ ∷ Δ₀) f (uf g) h refl | inj₂ (Δ₀ , refl , refl) = cong uf (ccut-ass-scut Δ₀ f g h refl)
    ccut-ass-scut Δ₀ f (Il g) h r = cong Il (ccut-ass-scut Δ₀ f g h r)
    ccut-ass-scut Δ₀ f (⊗l g) h refl = cong ⊗l (ccut-ass-scut (_ ∷ Δ₀) f g h refl)
    ccut-ass-scut Δ₀ f (switch-at g) h refl = ccut-ass-scutR Δ₀ f g h refl
    ccut-ass-scut Δ₀ f (switch-not g) h r = ⊥-elim ([]disj∷ Δ₀ r)

    ccut-ass-scutR : {T : StpR} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A B C : Fma}
      → (f : nothing ∣ Γ ⊢L A)(g : T ∣ Δ ⊢R B)(h : just B ∣ Δ'' ⊢L C)
      → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
      → ccut Δ₀ f (scutR g h) (cong₂ _++_ r (refl {x = Δ''})) ≡ scutR (ccutR Δ₀ f g r) h
    ccut-ass-scutR Δ₀ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-ass-scutR Δ₀ f Ir h r = ⊥-elim ([]disj∷ Δ₀ r)
    ccut-ass-scutR Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g') (⊗l h) r with cases++ Δ₀ Γ Δ' Δ r
    ccut-ass-scutR Δ₀ {_} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') (⊗l h) refl | inj₁ (Γ₀ , refl , refl) = ccut-ass-scutR Δ₀ f g (ccut [] g' h refl) refl
    ccut-ass-scutR .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') (⊗l h) refl | inj₂ (Γ₀ , refl , refl) =
      trans (sym (scutR-par-ccut Γ₀ g f (ccut [] g' h refl) refl))
        (cong (scutR g) (ccut-ass-ccut Γ₀ [] f g' h refl))
    ccut-ass-scutR Δ₀ f (⊗r[] g g') (⊗l h) refl =
      ccut-ass-scutR Δ₀ f g' (uf-1 (scutR g h)) refl

    ccut-ass-ccut : {T : Stp} → {Γ Δ : Cxt} → (Γ₀ Δ₀ : Cxt) → {Δ' Γ' : Cxt} → {A B C : Fma}
      → (f : nothing ∣ Γ ⊢L A)(g : nothing ∣ Γ₀ ++ A ∷ Γ' ⊢L B)(h : T ∣ Δ ⊢L C)
      → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
      → ccut (Δ₀ ++ Γ₀) f (ccut Δ₀ g h r) refl ≡ ccut Δ₀ (ccut Γ₀ f g refl) h r
    ccut-ass-ccut Γ₀ Δ₀ f g (uf h) r with cases∷ Δ₀ r
    ccut-ass-ccut Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = ccut-ass-scut Γ₀ f g h refl
    ccut-ass-ccut Γ₀ .(_ ∷ Δ₀') f g (uf h) r | inj₂ (Δ₀' , refl , refl) = cong uf (ccut-ass-ccut Γ₀ Δ₀' f g h refl)
    ccut-ass-ccut Γ₀ Δ₀ f g (Il h) r = cong Il (ccut-ass-ccut Γ₀ Δ₀ f g h r)
    ccut-ass-ccut Γ₀ Δ₀ f g (⊗l h) refl = cong ⊗l (ccut-ass-ccut Γ₀ (_ ∷ Δ₀) f g h refl)
    ccut-ass-ccut Γ₀ Δ₀ f g (switch-at h) refl = cong switch-at (ccutR-ass-ccutR Γ₀ Δ₀ f g h refl)
    ccut-ass-ccut Γ₀ Δ₀ f g (switch-not h) r = ⊥-elim ([]disj∷ Δ₀ r)

    ccutR-ass-ccutR : {T : StpR} → {Γ Δ : Cxt} → (Γ₀ Δ₀ : Cxt) → {Δ' Γ' : Cxt} → {A B C : Fma}
      → (f : nothing ∣ Γ ⊢L A)(g : nothing ∣ Γ₀ ++ A ∷ Γ' ⊢L B)(h : T ∣ Δ ⊢R C)
      → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
      → ccutR (Δ₀ ++ Γ₀) f (ccutR Δ₀ g h r) refl ≡ ccutR Δ₀ (ccut Γ₀ f g refl) h r
    ccutR-ass-ccutR Γ₀ Δ₀ f g ax r = ⊥-elim ([]disj∷ Δ₀ r)
    ccutR-ass-ccutR Γ₀ Δ₀ f g Ir r = ⊥-elim ([]disj∷ Δ₀ r)
    ccutR-ass-ccutR Γ₀ Δ₀ {Δ'} f g (⊗r {Γ = Γ} {Δ} h h') r with  cases++ Δ₀ Γ Δ' Δ r
    ccutR-ass-ccutR {Γ = Γ} Γ₀ Δ₀ {.(Γ₀' ++ Δ)} {Γ'} {A} f g (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀')} {Δ} h h') refl | inj₁ (Γ₀' , refl , refl)
      rewrite cases++-inj₁ (Δ₀ ++ Γ₀) (Γ' ++ Γ₀') Δ A = 
      cong₂ (⊗r {Γ = Δ₀ ++ Γ₀ ++ Γ ++ Γ' ++ Γ₀'}{Δ}) (ccutR-ass-ccutR Γ₀ Δ₀ f g h refl) refl
    ccutR-ass-ccutR Γ₀ .(Γ ++ Γ₀') {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Γ₀' ++ _ ∷ Δ')} h h') refl | inj₂ (Γ₀' , refl , refl) 
      rewrite cases++-inj₂ (Γ₀' ++ Γ₀) Γ (Γ' ++ Δ') A = cong (⊗r h) (ccut-ass-ccut Γ₀ Γ₀' f g h' refl)
    ccutR-ass-ccutR Γ₀ Δ₀ f g (⊗r[] h h') r = cong (⊗r[] h) (ccutR-ass-ccutR Γ₀ Δ₀ f g h' r)
    

⊗l-1-alt : {Γ : Cxt}{A B C : Fma}(f : just (A ⊗ B) ∣ Γ ⊢L C)
  → ⊗l-1 f ≡ scut (⊗rL axL (uf axL)) f
⊗l-1-alt (⊗l f) =
  sym
    (trans (scut-⊗rL-⊗l axL _ _)
      (trans (scut-axL1 _) (ccut-axL1 [] f refl)))


