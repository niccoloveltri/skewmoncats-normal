{-# OPTIONS --rewriting #-}

module MulticatLaws2 where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk
open import Cuts
open import MulticatLaws1


-- ====================================================================

-- Extra laws satisfied by the cut rules (e.g. associativity, parallel
-- composition, etc.), part 2.

-- ====================================================================

abstract




  scut-ass-scut : {S : Stp} → {Γ Δ Δ' : Cxt} → {A B C : Fma}
    → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
    → scut f (scut g h) ≗ scut (scut f g) h
  ccut-ass-scut : {b : Bool} {S T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A B C : Fma}
    → (f : S ∣ Γ ⊢ A)(g : T ∣ Δ ⊢ B)(h : just B ∣ Δ'' ⊢ C)
    → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
    → ccut b Δ₀ f (scut g h) (cong₂ _++_ r (refl {x = Δ''})) ≗ scut (ccut b Δ₀ f g r) h
  scut-let⊗ : {b : Bool}{S T : Stp} → {Γ : Cxt} (Γ₁ Γ₂ : Cxt) {Δ : Cxt} → {A C J J' : Fma} → 
              (f : S ∣ Γ ⊢ J ⊗ J')  (g : T ∣ Γ₁ ++ J ∷ J' ∷ Γ₂ ⊢ A) (h : just A ∣ Δ ⊢ C) →
              scut (let⊗ b Γ₁ Γ₂ f g) h ≗ let⊗ b Γ₁ (Γ₂ ++ Δ) f (scut g h)
  ccut-let⊗ : {b b' : Bool}{S₁ S₂ T : Stp} → {Γ Δ : Cxt} → (Δ₀ Λ₁ Λ₂ : Cxt) → {Δ' : Cxt} → {A C J J' : Fma} → 
             (f : S₁ ∣ Γ ⊢ A) (g : S₂ ∣ Δ ⊢ J ⊗ J') (h : T ∣ Λ₁ ++ J ∷ J' ∷ Λ₂ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
            ccut b' (Λ₁ ++ asCxt b S₂ Δ₀) f (let⊗ b Λ₁ Λ₂ (subst-cxt r g) h) refl ≗ let⊗ b Λ₁ Λ₂ (ccut b' Δ₀ f g r) h
  ccut-ass-ccut : {b b' : Bool} {S₁ S₂ T : Stp} → {Γ Δ : Cxt} → (Γ₀ Δ₀ : Cxt) → {Δ' Γ' : Cxt} → {A B C : Fma}
    → (f : S₁ ∣ Γ ⊢ A)(g : S₂ ∣ Γ₀ ++ A ∷ Γ' ⊢ B)(h : T ∣ Δ ⊢ C)
    → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
    → ccut b' (Δ₀ ++ asCxt b S₂ Γ₀) f (ccut b Δ₀ g h r) refl ≗ ccut b Δ₀ (ccut b' Γ₀ f g refl) h r
  let⊗-let⊗ : {b b' : Bool}{S₁ S₂ T : Stp} → {Γ : Cxt} → (Δ₁ Δ₂ Λ₁ Λ₂ : Cxt) → {C J J' K K' : Fma} →
            (f : S₁ ∣ Γ ⊢ J ⊗ J') (g : S₂ ∣ Δ₁ ++ J ∷ J' ∷ Δ₂ ⊢ K ⊗ K') (h : T ∣ Λ₁ ++ K ∷ K' ∷ Λ₂ ⊢ C) → 
            let⊗ b' (Λ₁ ++ asCxt b S₂ Δ₁) (Δ₂ ++ Λ₂) f (let⊗ b Λ₁ Λ₂ g h) ≗
              let⊗ b Λ₁ Λ₂ (let⊗ b' Δ₁ Δ₂ f g) h
  ccut-let⊗-s : {b b' : Bool} {S₁ T : Stp} → {Γ Δ : Cxt} → (Λ₁ Λ₂ : Cxt) → {A C  J J' : Fma} → 
              (f : S₁ ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ J ⊗ J') (h : T ∣ Λ₁ ++ J ∷ J' ∷ Λ₂ ⊢ C) → 
              ccut b Λ₁ f (let⊗ b' Λ₁ Λ₂ g h) refl ≗ let⊗ b Λ₁ Λ₂ (scut f g) h
  let⊗-let⊗-s : {b : Bool} {S T : Stp} → {Γ Δ : Cxt} → (Λ₁ Λ₂ : Cxt) → {C J J' K K' : Fma} →
              (f : S ∣ Γ ⊢ J ⊗ J') (g : just J ∣ J' ∷ Δ ⊢ K ⊗ K') (h : T ∣ Λ₁ ++ K ∷ K' ∷ Λ₂ ⊢ C) → 
              let⊗ b Λ₁ (Δ ++ Λ₂) f (let⊗ true Λ₁ Λ₂ g h) ≗ let⊗ false Λ₁ Λ₂ (let⊗ b [] Δ f (uf g)) h
  ccut-ass-ccut-s : {b b' : Bool} {S T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' Γ' : Cxt} → {A B C : Fma}
    → (f : S ∣ Γ ⊢ A)(g : just A ∣ Γ' ⊢ B)(h : T ∣ Δ ⊢ C)
    → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
    → ccut b Δ₀ f (ccut b' Δ₀ g h r) refl ≗ ccut b Δ₀ (scut f g) h r


  let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ ax g h = refl
  let⊗-let⊗ {b} {false} Δ₁ Δ₂ Λ₁ Λ₂ (uf f) g h = let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h
  let⊗-let⊗ {b} {true}{S₂ = S₂} Δ₁ Δ₂ Λ₁ Λ₂ (uf {Γ = Γ} f) g h =
    cong-Ic (Λ₁ ++ asCxt b S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂) (let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h) refl
    ∙ ≡-to-≗ (sym (let⊗-Ic1 b Δ₁ Λ₁ Λ₂ (Γ ++ Δ₂) (let⊗ true Δ₁ Δ₂ f g) h refl))  
  let⊗-let⊗ {b}{S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (⊗r f f') g h =
    cong-ccut2 (Λ₁ ++ asCxt b S₂ Δ₁) {f = f} refl (ccut-let⊗ (Δ₁ ++ _ ∷ [])  Λ₁ Λ₂ f' g h refl)
    ∙ ccut-let⊗ Δ₁ Λ₁ Λ₂ f (ccut false (Δ₁ ++ _ ∷ []) f' g refl) h refl
  let⊗-let⊗ {S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (Il f) g h = let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h
  let⊗-let⊗ {b}{S₂ = S₂} {Γ = Γ} Δ₁ Δ₂ Λ₁ Λ₂ (⊗l f) g h =
    ⊗c (Λ₁ ++ asCxt b S₂ Δ₁) (Γ ++ Δ₂ ++ Λ₂) (let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
  let⊗-let⊗ {b}{b'}{S₁} {S₂} Δ₁ Δ₂ Λ₁ Λ₂ (⊗c Γ Δ f) g h = 
    ⊗c (Λ₁ ++ asCxt b S₂ Δ₁ ++ asCxt b' S₁ Γ) (Δ ++ Δ₂ ++ Λ₂) (let⊗-let⊗ Δ₁ Δ₂ Λ₁ Λ₂ f g h)
  
  ccut-let⊗-s Λ₁ Λ₂ {J = J}{J'} f ax h
    rewrite cases++-inj₂ [] Λ₁ Λ₂ (J ⊗ J') = ≡-to-≗ (cong (λ x → let⊗ _ Λ₁ Λ₂ x h) (sym (scut-unit f)))
  ccut-let⊗-s Λ₁ Λ₂ {J = J}{J'} f (⊗r g g') h = 
    ccut-ass-ccut-s Λ₁ f g (ccut false (Λ₁ ++ _ ∷ []) g' h refl) refl
      ∙ (~ cong-let⊗1 Λ₁ Λ₂ h (scut⊗r f g g'))
  ccut-let⊗-s {b} {S₁ = S₁} {Δ = Δ} Λ₁ Λ₂ f (Il g) h = ccut-let⊗-s-true Λ₁ Λ₂ f g h
  ccut-let⊗-s {false} {S₁ = nothing} {Δ = Δ} Λ₁ Λ₂ f (⊗l {A = A} {B} g) h 
    rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂)  (A ⊗ B) =
    ≡-to-≗ (cong (let⊗ _ Λ₁ (Δ ++ Λ₂) f) (let⊗-bool {b' = true}  Λ₁ Λ₂ g h))
    ∙ let⊗-let⊗-s Λ₁ Λ₂ f g h
    ∙ cong-let⊗1 Λ₁ Λ₂ h (let⊗-[] Δ f g)
  ccut-let⊗-s {true} {S₁ = nothing} {Δ = Δ} Λ₁ Λ₂ f (⊗l {A = A} {B} g) h 
    rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂)  (A ⊗ B) =
    ≡-to-≗ (cong (let⊗ _ Λ₁ (Δ ++ Λ₂) f) (let⊗-bool {b' = true}  Λ₁ Λ₂ g h))
    ∙ let⊗-let⊗-s Λ₁ Λ₂ f g h
    ∙ cong-let⊗1 Λ₁ Λ₂ h (let⊗-[]-true Δ f g)
  ccut-let⊗-s {S₁ = just A'} {Δ = Δ} Λ₁ Λ₂ f (⊗l {A = A} {B} g) h 
    rewrite cases++-inj₂ [] Λ₁ (Δ ++ Λ₂)  (A ⊗ B) = 
    ≡-to-≗ (cong (let⊗ _ Λ₁ (Δ ++ Λ₂) f) (let⊗-bool {b' = true}  Λ₁ Λ₂ g h))
    ∙ let⊗-let⊗-s Λ₁ Λ₂ f g h
    ∙ cong-let⊗1 Λ₁ Λ₂ h (let⊗-[]-j Δ f g)
    ∙ ≡-to-≗ (let⊗-bool {b = false} Λ₁ Λ₂ (scut f (⊗l g)) h)
  ccut-let⊗-s {b}{b'}{S₁}{Γ = Γ₁} Λ₁ Λ₂ {A} f (⊗c Γ Δ {J = J}{J'} g) h
    rewrite cases++-inj₁ Λ₁ Γ (Δ ++ Λ₂) A | cases++-inj₁ Λ₁ Γ (J ⊗ J' ∷ Δ ++ Λ₂) A =
    ⊗c (Λ₁ ++ asCxt b S₁ Γ₁ ++ Γ) (Δ ++ Λ₂) (ccut-let⊗-s Λ₁ Λ₂ f g h)
    ∙ cong-let⊗1 Λ₁ Λ₂ h (~ scut-⊗c Γ Δ f g) 

  ccut-ass-ccut-s Δ₀ f g ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ass-ccut-s Δ₀ f g (uf h) r with cases∷ Δ₀ r
  ccut-ass-ccut-s {false} {b'} {nothing} .[] f g (uf h) refl | inj₁ (refl , refl , refl) = scut-ass-scut f g h
  ccut-ass-ccut-s {true} {b'} {nothing} .[] f g (uf h) refl | inj₁ (refl , refl , refl) = uf (Il (scut-ass-scut f g h))
  ccut-ass-ccut-s {b}{b'}{just x} .[] f g (uf h) refl | inj₁ (refl , refl , refl) = uf (scut-ass-scut f g h)
  ccut-ass-ccut-s .(_ ∷ Γ₀) f g (uf h) refl | inj₂ (Γ₀ , refl , refl) =
    uf (ccut-ass-ccut-s Γ₀ f g h refl)
  ccut-ass-ccut-s Δ₀ f g Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ass-ccut-s Δ₀ {Δ'} f g (⊗r {Γ = Γ}{Δ} h h₁) r with cases++ Δ₀ Γ Δ' Δ r 
  ccut-ass-ccut-s Δ₀ {.(Γ₀ ++ Δ)} {Γ'} {A} f g (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} h h₁) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Γ' ++ Γ₀) Δ A = ⊗r (ccut-ass-ccut-s Δ₀ f g h refl) refl
  ccut-ass-ccut-s .(Γ ++ Γ₀) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} h h₁) refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ (Γ' ++ Δ') A = ⊗r refl (ccut-ass-ccut-s Γ₀ f g h₁ refl)
  ccut-ass-ccut-s Δ₀ f g (Il h) refl = Il (ccut-ass-ccut-s Δ₀ f g h refl)
  ccut-ass-ccut-s Δ₀ f g (⊗l h) refl = ⊗l (ccut-ass-ccut-s (_ ∷ Δ₀) f g h refl)
  ccut-ass-ccut-s Δ₀ {Δ'} f g (⊗c Γ Δ h) r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
  ccut-ass-ccut-s {b}{b'}{S}{Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} {Γ'} {A} f g (⊗c .(Δ₀ ++ _ ∷ Γ₀) Δ {J = J}{J'} h) refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ (Γ' ++ Γ₀) (J ⊗ J' ∷ Δ) A = ⊗c (Δ₀ ++ asCxt b S Γ ++ Γ' ++ Γ₀) Δ (ccut-ass-ccut-s Δ₀ f g h refl)
  ccut-ass-ccut-s .Γ {.Δ} f g (⊗c Γ Δ h) refl | inj₂ ([] , refl , refl) = ccut-let⊗-s Γ Δ f g h
  ccut-ass-ccut-s {b}{b'}{S}{Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} {Γ'} {A} f g (⊗c Γ .(Γ₀ ++ _ ∷ Δ'){J = J}{J'} h) refl | inj₂ (_ ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (Γ' ++ Δ') A = ⊗c Γ (Γ₀ ++ asCxt b S Γ₁ ++ Γ' ++ Δ') (ccut-ass-ccut-s (Γ ++ _ ∷ _ ∷ Γ₀) f g h refl)

  let⊗-let⊗-s {Δ = Δ} Λ₁ Λ₂ ax g h =
    ≡-to-≗ (cong (⊗c Λ₁ (Δ ++ Λ₂)) (let⊗-bool Λ₁ Λ₂ g h))
  let⊗-let⊗-s {false} Λ₁ Λ₂ (uf f) g h = let⊗-let⊗-s Λ₁ Λ₂ f g h
  let⊗-let⊗-s {true} {Δ = Δ} Λ₁ Λ₂ (uf {Γ} f) g h =
    cong-Ic Λ₁ (Γ ++ Δ ++ Λ₂) (let⊗-let⊗-s Λ₁ Λ₂ f g h) refl
    ∙ ≡-to-≗ (sym (let⊗-Ic1 false [] Λ₁ Λ₂ (Γ ++ Δ) (let⊗ true [] Δ f (uf g)) h refl))
  let⊗-let⊗-s {false} {nothing} {Δ} Λ₁ Λ₂ (⊗r {Γ = Γ} f f₁) g h = 
    ≡-to-≗ (ccut-par-ccut Λ₁ f f₁ (let⊗ true Λ₁ Λ₂ g h) refl)
    ∙ cong-ccut2 (Λ₁ ++ Γ) {f = f₁} refl (ccut-let⊗-s Λ₁ Λ₂ f g h)
    ∙ ccut-let⊗ Γ Λ₁ Λ₂ f₁ (scut f g) h refl
    ∙ ≡-to-≗ (cong (λ x → let⊗ false Λ₁ Λ₂ x h) (sym (scut-par-ccut [] f f₁ g refl)))
  let⊗-let⊗-s {true} {nothing} {Δ} Λ₁ Λ₂ (⊗r {Γ = Γ} f f₁) g h = 
    ≡-to-≗ (ccut-par-ccut Λ₁ f f₁ (let⊗ true Λ₁ Λ₂ g h) refl)
    ∙ cong-ccut2 (Λ₁ ++ I ∷ Γ) {f = f₁} refl (ccut-let⊗-s Λ₁ Λ₂ f g h)
    ∙ ccut-let⊗ Γ Λ₁ Λ₂ f₁ (scut f g) h refl
    ∙ ≡-to-≗ (cong (λ x → let⊗ true Λ₁ Λ₂ x h) (sym (scut-par-ccut [] f f₁ g refl)))
  let⊗-let⊗-s {b}{S = just A} {Δ} Λ₁ Λ₂ (⊗r {Γ = Γ} f f₁) g h = 
    ≡-to-≗ (ccut-par-ccut Λ₁ f f₁ (let⊗ true Λ₁ Λ₂ g h) refl)
    ∙ cong-ccut2 (Λ₁ ++ _ ∷ Γ) {f = f₁} refl (ccut-let⊗-s Λ₁ Λ₂ f g h)
    ∙ ccut-let⊗ Γ Λ₁ Λ₂ f₁ (scut f g) h refl
    ∙ ≡-to-≗ (trans (cong (λ x → let⊗ b Λ₁ Λ₂ x h) (sym (scut-par-ccut [] f f₁ g refl))) (let⊗-bool Λ₁ Λ₂ (scut f (ccut false [] f₁ g refl)) h))
  let⊗-let⊗-s {Γ = Γ} {Δ} Λ₁ Λ₂ (Il f) g h = let⊗-let⊗-s Λ₁ Λ₂ f g h
  let⊗-let⊗-s {Γ = Γ} {Δ} Λ₁ Λ₂ (⊗l f) g h = 
    ⊗c Λ₁ (Γ ++ Δ ++ Λ₂) (let⊗-let⊗-s Λ₁ Λ₂ f g h)
  let⊗-let⊗-s {b}{S} {Δ = Δ₁} Λ₁ Λ₂ (⊗c Γ Δ f) g h = 
    ⊗c (Λ₁ ++ asCxt b S Γ) (Δ ++ Δ₁ ++ Λ₂) (let⊗-let⊗-s Λ₁ Λ₂ f g h)

  scut-ass-scut ax g h = refl
  scut-ass-scut (uf f) g h = uf (scut-ass-scut f g h)
  scut-ass-scut Ir g h = ≡-to-≗ (
    begin
    scut Ir (scut g h)
    ≡⟨ sym (Il-1-scutIr (scut g h)) ⟩
    Il-1 (scut g h)
    ≡⟨ scutIl-1 g h ⟩
    scut (Il-1 g) h
    ≡⟨ cong (λ x → scut x h) (Il-1-scutIr g) ⟩
    scut (scut Ir g) h
    ∎)
  scut-ass-scut (⊗r f f') ax h = refl
  scut-ass-scut (⊗r f f') (⊗r g g') ax = refl
  scut-ass-scut (⊗r {Γ = Γ} {Δ} f f') (⊗r {Γ = Γ₁} {Δ₁} g g') (⊗r {Γ = Γ₂} {Δ₂} h h') =
    ⊗r {Γ = Γ ++ Δ ++ Γ₁ ++ Δ₁ ++ Γ₂}{Δ₂} (scut-ass-scut (⊗r f f') (⊗r g g') h) refl
  scut-ass-scut (⊗r {Γ = Γ'}{Δ'} f f') (⊗r {Γ = Γ} g g') (⊗l h) =
    scut-ass-scut (⊗r f f') g (ccut false [] g' h refl)
  scut-ass-scut (⊗r {Γ = Γ'} {Δ'} f f') (⊗r {Γ = Γ''} {Δ₁} g g') (⊗c Γ Δ h) =
    ⊗c (Γ' ++ Δ' ++ Γ'' ++ Δ₁ ++ Γ) Δ (scut-ass-scut (⊗r f f') (⊗r g g') h)
  scut-ass-scut {Δ' = Δ'} (⊗r {Γ = Γ₁} {Δ₁} f f') (⊗c Γ Δ g) h =
    ⊗c (Γ₁ ++ Δ₁ ++ Γ) (Δ ++ Δ') (scut-ass-scut (⊗r f f') g h)
  scut-ass-scut (⊗r {Γ = Γ} f f') (⊗l g) h = 
    cong-scut2 f (ccut-ass-scut [] f' g h refl)
    ∙ scut-ass-scut f (ccut false [] f' g refl) h
  scut-ass-scut (Il f) g h = Il (scut-ass-scut f g h)
  scut-ass-scut (⊗l f) g h = ⊗l (scut-ass-scut f g h)
  scut-ass-scut {Δ = Δ₁} {Δ'} (⊗c Γ Δ f) g h =
    ⊗c Γ (Δ ++ Δ₁ ++ Δ') (scut-ass-scut f g h)

  ccut-ass-scut Δ₀ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ass-scut Δ₀ f (uf g) h r with cases∷ Δ₀ r
  ccut-ass-scut {false} {nothing} .[] f (uf g) h refl | inj₁ (refl , refl , refl) = scut-ass-scut f g h
  ccut-ass-scut {true} {nothing} .[] f (uf g) h refl | inj₁ (refl , refl , refl) = uf (Il (scut-ass-scut f g h)) 
  ccut-ass-scut {_}{just x} .[] f (uf g) h refl | inj₁ (refl , refl , refl) = uf (scut-ass-scut f g h) 
  ccut-ass-scut .(_ ∷ Γ₀) f (uf g) h refl | inj₂ (Γ₀ , refl , refl) =
    uf (ccut-ass-scut Γ₀ f g h refl)
  ccut-ass-scut Δ₀ f Ir h r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ass-scut Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g') h r with cases++ Δ₀ Γ Δ' Δ r
  ccut-ass-scut Δ₀ {.(Γ₀ ++ Δ)} {A = A} f (⊗r {Γ = .(Δ₀ ++ A ∷ Γ₀)} {Δ} g g') ax refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ Γ₀ Δ A = refl
  ccut-ass-scut {b}{S} {Γ = Γ₁} Δ₀ {A = A} f (⊗r {Γ = _} {Δ} g g') (⊗r {Γ = Γ} {Δ₁} h h₁) refl | inj₁ (Γ₀ , refl , refl) with ccut-ass-scut Δ₀ f (⊗r g g') h refl
  ... | ih 
    rewrite cases++-inj₁ Δ₀ (Γ₀ ++ Δ ++ Γ) Δ₁ A | cases++-inj₁ Δ₀ Γ₀ Δ A = 
    ⊗r {Γ = Δ₀ ++ asCxt b S Γ₁ ++ Γ₀ ++ Δ ++ Γ} ih refl
  ccut-ass-scut Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') (⊗l h) refl | inj₁ (Γ₀ , refl , refl) =
    ccut-ass-scut Δ₀ f g (ccut false [] g' h refl) refl
  ccut-ass-scut {b}{S} {Γ = Γ₁} Δ₀ {A = A} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') (⊗c Γ Δ₁ {J} {J'} h) refl | inj₁ (Γ₀ , refl , refl) with ccut-ass-scut Δ₀ f (⊗r g g') h refl
  ... | ih
    rewrite cases++-inj₁ Δ₀ (Γ₀ ++ Δ ++ Γ) (J ⊗ J' ∷ Δ₁) A | cases++-inj₁ Δ₀ Γ₀ Δ A =
    ⊗c (Δ₀ ++ asCxt b S Γ₁ ++ Γ₀ ++ Δ ++ Γ) Δ₁ ih
  ccut-ass-scut .(Γ ++ Γ₀) {Δ'} {A = A} f (⊗r {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} g g') ax refl | inj₂ (Γ₀ , refl , refl)
    rewrite cases++-inj₂ Γ₀ Γ Δ' A = refl
  ccut-ass-scut {b}{S} {Γ = Γ₂} ._ {Δ'} {A = A} f (⊗r {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} g g') (⊗r {Γ = Γ₁} {Δ} h h₁) refl | inj₂ (Γ₀ , refl , refl) with ccut-ass-scut (Γ ++ Γ₀) f (⊗r g g') h refl
  ... | ih 
    rewrite cases++-inj₁ (Γ ++ Γ₀) (Δ' ++ Γ₁) Δ A | cases++-inj₂ Γ₀ Γ Δ' A =
    ⊗r {Γ = Γ ++ Γ₀ ++ asCxt b S Γ₂ ++ Δ' ++ Γ₁} ih refl
  ccut-ass-scut .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') (⊗l h) refl | inj₂ (Γ₀ , refl , refl) =
    ~ (≡-to-≗ (scut-par-ccut Γ₀ g f (ccut false [] g' h refl) refl)) ∙ 
      (cong-scut2 g (ccut-ass-ccut Γ₀ [] f g' h refl))
  ccut-ass-scut {b}{S} {Γ = Γ₂} .(Γ ++ Γ₀) {Δ'} {A = A} f (⊗r {Γ = Γ} g g') (⊗c Γ₁ Δ {J} {J'} h) refl | inj₂ (Γ₀ , refl , refl) with ccut-ass-scut (Γ ++ Γ₀) f (⊗r g g') h refl
  ... | ih
    rewrite cases++-inj₁ (Γ ++ Γ₀) (Δ' ++ Γ₁) (J ⊗ J' ∷ Δ) A | cases++-inj₂ Γ₀ Γ Δ' A =
    ⊗c (Γ ++ Γ₀ ++ asCxt b S Γ₂ ++ Δ' ++ Γ₁) Δ ih
  ccut-ass-scut Δ₀ f (Il g) h refl = Il (ccut-ass-scut Δ₀ f g h refl)
  ccut-ass-scut Δ₀ f (⊗l {B = B} g) h refl = ⊗l (ccut-ass-scut (B ∷ Δ₀) f g h refl)
  ccut-ass-scut Δ₀ {Δ'} f (⊗c Γ Δ g) h r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
  ccut-ass-scut {b}{S}{Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ Δ)} {Δ''} {A} f (⊗c .(Δ₀ ++ A ∷ Γ₀) Δ {J = J}{J'} g) h refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ Δ₀ Γ₀ (J ⊗ J' ∷ Δ ++ Δ'') A =
    ⊗c (Δ₀ ++ asCxt b S Γ ++ Γ₀) (Δ ++ Δ'') (ccut-ass-scut Δ₀ f g h refl)
  ccut-ass-scut .Γ {.Δ} {Δ''} f (⊗c Γ Δ {J = J}{J'} g) h refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] Γ (Δ ++ Δ'') (J ⊗ J') = ~ (scut-let⊗ Γ Δ f g h)
  ccut-ass-scut {b}{S} {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) {Δ'} {Δ''} {A} f (⊗c Γ .(Γ₀ ++ A ∷ Δ') {J = J}{J'} g) h refl | inj₂ (_ ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) Γ (Δ' ++ Δ'') A =
    ⊗c Γ (Γ₀ ++ asCxt b S Γ₁ ++ Δ' ++ Δ'') (ccut-ass-scut (Γ ++ _ ∷ _ ∷ Γ₀) f g h refl)

  scut-let⊗ Γ₁ Γ₂ ax g h = refl
  scut-let⊗ {false} Γ₁ Γ₂ (uf f) g h = scut-let⊗ Γ₁ Γ₂ f g h
  scut-let⊗ {true} Γ₁ Γ₂ {Δ} (uf {Γ = Γ} f) g h =
    ≡-to-≗ (scut-Ic1 Γ₁ (Γ ++ Γ₂) (let⊗ true Γ₁ Γ₂ f g) h refl) ∙ cong-Ic Γ₁ (Γ ++ Γ₂ ++ Δ) (scut-let⊗ Γ₁ Γ₂ f g h) refl
  scut-let⊗ Γ₁ Γ₂ (⊗r f f') g h =
    ~ (_∙_ (cong-ccut2 Γ₁ {f = f} refl (ccut-ass-scut (Γ₁ ++ _ ∷ []) f' g h refl))
      (ccut-ass-scut Γ₁ f (ccut false (Γ₁ ++ _ ∷ []) f' g refl) h refl))
  scut-let⊗ {Γ = Γ} Γ₁ Γ₂ {Δ} (Il f) g h = scut-let⊗ Γ₁ Γ₂ f g h
  scut-let⊗ {Γ = Γ} Γ₁ Γ₂ {Δ} (⊗l f) g h = ⊗c Γ₁ (Γ ++ Γ₂ ++ Δ) (scut-let⊗ Γ₁ Γ₂ f g h)
  scut-let⊗ {b}{S} Γ₁ Γ₂ {Δ₁} (⊗c Γ Δ f) g h = ⊗c (Γ₁ ++ asCxt b S Γ) (Δ ++ Γ₂ ++ Δ₁) (scut-let⊗ Γ₁ Γ₂ f g h)

  ccut-let⊗ Δ₀ Λ₁ Λ₂ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-let⊗ Δ₀ Λ₁ Λ₂ f (uf g) h r with cases∷ Δ₀ r
  ccut-let⊗ {false} {false} {nothing} .[] Λ₁ Λ₂ f (uf g) h refl | inj₁ (refl , refl , refl) = ccut-let⊗-s Λ₁ Λ₂ f g h
  ccut-let⊗ {false} {true} {nothing} .[] Λ₁ Λ₂ f (uf g) h refl | inj₁ (refl , refl , refl) = ccut-let⊗-s Λ₁ Λ₂ f g h
  ccut-let⊗ {true} {false} {nothing} .[] Λ₁ Λ₂ f (uf g) h refl | inj₁ (refl , refl , refl) =
    ≡-to-≗ (ccut-Ic2-n-false Λ₁ f (let⊗ true Λ₁ Λ₂ g h) refl)
    ∙ ccut-let⊗-s {_}{true} Λ₁ Λ₂ f g h
  ccut-let⊗ {true} {true} {nothing} {Γ = Γ} .[] Λ₁ Λ₂ f (uf {Γ = Γ₁} g) h refl | inj₁ (refl , refl , refl) =
    ≡-to-≗ (ccut-Ic2-n-true Λ₁ f (let⊗ true Λ₁ Λ₂ g h) refl)
    ∙ cong-Ic Λ₁ (Γ ++ Γ₁ ++ Λ₂) (ccut-let⊗-s {_}{true} Λ₁ Λ₂ f g h) refl
  ccut-let⊗ {false} {b'} {just x} .[] Λ₁ Λ₂ f (uf g) h refl | inj₁ (refl , refl , refl) =
    ccut-let⊗-s Λ₁ Λ₂ f g h ∙ ≡-to-≗ (let⊗-bool Λ₁ Λ₂ (scut f g) h)
  ccut-let⊗ {true} {b'} {just x} {Γ = Γ} .[] Λ₁ Λ₂ f (uf {Γ₁} g) h refl | inj₁ (refl , refl , refl) =
    ≡-to-≗ (trans (ccut-Ic2-j Λ₁ f (let⊗ true Λ₁ Λ₂ g h) refl) (cong (λ x → Ic Λ₁ (Γ ++ Γ₁ ++ Λ₂) x refl) (ccut-bool Λ₁ f (let⊗ true Λ₁ Λ₂ g h) refl)))
    ∙ cong-Ic Λ₁ (Γ ++ Γ₁ ++ Λ₂) (ccut-let⊗-s {_}{true} Λ₁ Λ₂ f g h) refl
  ccut-let⊗ {false} .(_ ∷ Γ₀) Λ₁ Λ₂ f (uf g) h refl | inj₂ (Γ₀ , refl , refl) = ccut-let⊗ Γ₀ Λ₁ Λ₂ f g h refl
  ccut-let⊗ {true}{b'}{S₁} {Γ = Γ} .(_ ∷ Γ₀) Λ₁ Λ₂ {Δ'} f (uf g) h refl | inj₂ (Γ₀ , refl , refl) =
    ≡-to-≗ (ccut-Ic22 _ Λ₁ Γ₀ f (let⊗ true Λ₁ Λ₂ g h) refl)
    ∙ cong-Ic Λ₁ (Γ₀ ++ asCxt b' S₁ Γ ++ Δ' ++ Λ₂) (ccut-let⊗ Γ₀ Λ₁ Λ₂ f g h refl) refl 
  ccut-let⊗ Δ₀ Λ₁ Λ₂ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') h r with cases++ Δ₀ Γ Δ' Δ r
  ccut-let⊗ Δ₀ Λ₁ Λ₂ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') h refl | inj₁ (Γ₀ , refl , refl) =
    ccut-ass-ccut Δ₀ Λ₁ f g (ccut _ (Λ₁ ++ _ ∷ []) g' h refl) refl
  ccut-let⊗ .(Γ ++ Γ₀) Λ₁ Λ₂ {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') h refl | inj₂ (Γ₀ , refl , refl) =
    ≡-to-≗ (sym (ccut-par-ccut Λ₁ g f (ccut false (Λ₁ ++ _ ∷ []) g' h refl) refl))
    ∙ cong-ccut2 Λ₁ {f = g} refl (ccut-ass-ccut Γ₀ (Λ₁ ++ _ ∷ []) f g' h refl)
  ccut-let⊗ {_}{_}{S₁}{Γ = Γ} Δ₀ Λ₁ Λ₂ {Δ'} {A} f (Il g) h refl = ccut-let⊗ Δ₀ Λ₁ Λ₂ f g h refl
  ccut-let⊗ {b}{b'} {S₁} {Γ = Γ} Δ₀ Λ₁ Λ₂ {Δ'} {A} f (⊗l {A = A₁} {B} g) h refl
    rewrite cases++-inj₂ (A₁ ⊗ B ∷ Δ₀) Λ₁ (Δ' ++ Λ₂) A = 
    ⊗c Λ₁ (Δ₀ ++ asCxt b' S₁ Γ ++ Δ' ++ Λ₂) (ccut-let⊗ (_ ∷ Δ₀) Λ₁ Λ₂ f g h refl)
  ccut-let⊗ Δ₀ Λ₁ Λ₂ {Δ'} f (⊗c Γ Δ g) h r with  cases++ Δ₀ Γ Δ' (_ ∷ Δ) r
  ccut-let⊗ {b}{b'}{S₁}{S₂}{Γ = Γ} Δ₀ Λ₁ Λ₂ {.(Γ₀ ++ _ ∷ Δ)} {A} f (⊗c .(Δ₀ ++ A ∷ Γ₀) Δ {J = J}{J'} g) h refl | inj₁ (Γ₀ , refl , refl)
    rewrite cases++-inj₁ (Λ₁ ++ asCxt b S₂ Δ₀) Γ₀  (J ⊗ J' ∷ Δ ++ Λ₂) A =
    ⊗c (Λ₁ ++ asCxt b S₂ Δ₀ ++ asCxt b' S₁ Γ ++ Γ₀) (Δ ++ Λ₂) (ccut-let⊗ Δ₀ Λ₁ Λ₂ f g h refl)
  ccut-let⊗ {b}{b'}{S₂ = S₂} .Γ Λ₁ Λ₂ {.Δ} f (⊗c Γ Δ {J = J}{J' } g) h refl | inj₂ ([] , refl , refl)
    rewrite cases++-inj₂ [] (Λ₁ ++ asCxt b S₂ Γ) (Δ ++ Λ₂) (J ⊗ J') = let⊗-let⊗ Γ Δ Λ₁ Λ₂ f g h
  ccut-let⊗ {b}{b'}{S₁} {S₂} {Γ = Γ₁} .(Γ ++ _ ∷ Γ₀) Λ₁ Λ₂ {Δ'} {A} f (⊗c Γ .(Γ₀ ++ A ∷ Δ') {J = J}{J'} g) h refl | inj₂ (_ ∷ Γ₀ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Γ₀) (Λ₁ ++ asCxt b S₂ Γ) (Δ' ++ Λ₂) A =
    ⊗c (Λ₁ ++ asCxt b S₂ Γ) (Γ₀ ++ asCxt b' S₁ Γ₁ ++ Δ' ++ Λ₂) (ccut-let⊗ (Γ ++ _ ∷ _ ∷ Γ₀) Λ₁ Λ₂ f g h refl)

  ccut-ass-ccut Γ₀ Δ₀ f g ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ass-ccut Γ₀ Δ₀ f g (uf h) r with cases∷ Δ₀ r
  ccut-ass-ccut {_}{_}{S₁} {just x} Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = uf (ccut-ass-scut Γ₀ f g h refl) 
  ccut-ass-ccut {false} {b'} {S₁} {nothing} Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = ccut-ass-scut Γ₀ f g h refl
  ccut-ass-ccut {true} {b'} {S₁} {nothing} Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = uf (Il (ccut-ass-scut Γ₀ f g h refl))
  ccut-ass-ccut Γ₀ .(_ ∷ Δ₀) f g (uf h) r | inj₂ (Δ₀ , refl , refl) = uf (ccut-ass-ccut Γ₀ Δ₀ f g h refl)
  ccut-ass-ccut Γ₀ Δ₀ f g Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-ass-ccut Γ₀ Δ₀ {Δ'} f g (⊗r {Γ = Γ}{Δ} h h') r with cases++ Δ₀ Γ Δ' Δ r
  ccut-ass-ccut {b}{b'}{S₁}{S₂}{Γ = Γ} Γ₀ Δ₀ {.(Λ ++ Δ)} {Γ'} {A} f g (⊗r {Γ = .(Δ₀ ++ _ ∷ Λ)} {Δ} h h') r | inj₁ (Λ , refl , refl)
    rewrite cases++-inj₁ (Δ₀ ++ asCxt b S₂ Γ₀) (Γ' ++ Λ) Δ A =
    ⊗r {Γ = Δ₀ ++ asCxt b S₂ Γ₀ ++ asCxt b' S₁ Γ ++ Γ' ++ Λ}{Δ} (ccut-ass-ccut Γ₀ Δ₀ f g h refl) refl
  ccut-ass-ccut {b}{b'}{S₁} {S₂} Γ₀ .(Γ ++ Λ) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Λ ++ _ ∷ Δ')} h h') r | inj₂ (Λ , refl , refl)
    rewrite cases++-inj₂ (Λ ++ asCxt b S₂ Γ₀) Γ (Γ' ++ Δ') A = ⊗r refl (ccut-ass-ccut Γ₀ Λ f g h' refl)
  ccut-ass-ccut Γ₀ Δ₀ f g (Il h) refl = Il (ccut-ass-ccut Γ₀ Δ₀ f g h refl)
  ccut-ass-ccut Γ₀ Δ₀ f g (⊗l {B = B} h) refl = ⊗l (ccut-ass-ccut Γ₀ (B ∷ Δ₀) f g h refl)
  ccut-ass-ccut Γ₀ Δ₀ {Δ'} f g (⊗c Γ Δ h) r with cases++ Δ₀ Γ Δ' (_ ∷ Δ) r 
  ccut-ass-ccut {b}{b'}{S₁}{S₂}{Γ = Γ} Γ₀ Δ₀ {.(Λ ++ _ ∷ Δ)} {Γ'} {A} f g (⊗c .(Δ₀ ++ _ ∷ Λ) Δ {J = J}{J'} h) refl | inj₁ (Λ , refl , refl)
    rewrite cases++-inj₁ (Δ₀ ++ asCxt b S₂ Γ₀) (Γ' ++ Λ) (J ⊗ J' ∷ Δ) A = 
    ⊗c (Δ₀ ++ asCxt b S₂ Γ₀ ++ asCxt b' S₁ Γ ++ Γ' ++ Λ) Δ (ccut-ass-ccut Γ₀ Δ₀ f g h refl)
  ccut-ass-ccut Γ₀ .Γ {.Δ} f g (⊗c Γ Δ  {J = J}{J'} h) refl | inj₂ ([] , refl , refl) = ccut-let⊗ Γ₀ Γ Δ f g h refl
  ccut-ass-ccut {b}{b'}{S₁} {S₂} {Γ = Γ₁} Γ₀ .(Γ ++ _ ∷ Λ) {Δ'} {Γ'} {A} f g (⊗c Γ .(Λ ++ _ ∷ Δ')  {J = J}{J'} h) refl | inj₂ (_ ∷ Λ , refl , refl)
    rewrite cases++-inj₂ (J ⊗ J' ∷ Λ ++ asCxt b S₂ Γ₀) Γ (Γ' ++ Δ') A = 
    ⊗c Γ (Λ ++ asCxt b S₂ Γ₀ ++ asCxt b' S₁ Γ₁ ++ Γ' ++ Δ') (ccut-ass-ccut Γ₀ (Γ ++ _ ∷ _ ∷ Λ) f g h refl)


