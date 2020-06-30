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
open import Cuts
open import MulticatLaws
open import Complete
open import StrongComplete
open import Sound
open import EqComplete
open import SoundComplete



-- ====================================================================

-- The function strcmplt sends ≐-related derivations into ≗-related
-- derivations

cong-strcmplt : {S : Stp}{Γ : Cxt}{C : Fma}{f g : 〈 S ∣ Γ 〉 ⇒ C} → f ≐ g →
                strcmplt {S}{Γ} f ≗ strcmplt g
cong-strcmplt {S}{Γ} p = cong⊗l-1⋆ {S} {Γ} (cong-cmplt p)

-- Ic and ⊗c permute with ⊗l⋆

Ic⊗l⋆ : (S : Stp) (Γ Γ₀ Γ₁ : Cxt) {C : Fma}
    → {f : S ∣ Γ ++ Γ₀ ++ Γ₁ ⊢ C}
    → Ic Γ₀ Γ₁ (⊗l⋆ S Γ f) ≗ ⊗l⋆ S Γ (Ic (Γ ++ Γ₀) Γ₁ f)
Ic⊗l⋆ (just x) [] Γ₀ Γ₁ = refl
Ic⊗l⋆ (just x) (x₁ ∷ Γ) Γ₀ Γ₁ =
  Ic⊗l⋆ (just (x ⊗ x₁)) Γ Γ₀ Γ₁
  ∙ cong⊗l⋆ {just (x ⊗ x₁)} {Γ} (~ ⊗lIc {Γ = Γ ++ Γ₀})
Ic⊗l⋆ nothing [] Γ₀ Γ₁ = ~ IlIc
Ic⊗l⋆ nothing (x ∷ Γ) Γ₀ Γ₁ = 
  Ic⊗l⋆ (just (I ⊗ x)) Γ Γ₀ Γ₁
  ∙ cong⊗l⋆ {just (I ⊗ x)} {Γ}
      (~ ⊗lIc {Γ = Γ ++ Γ₀}
       ∙ ⊗l (~ IlIc))

⊗c⊗l⋆ : (S : Stp) (Γ Γ₀ Γ₁ : Cxt){C J J' : Fma}{cJ : isCl J}{cJ' : isCl J'}
    → {f : S ∣ Γ ++ Γ₀ ++ J ∷ J' ∷ Γ₁ ⊢ C}
    → ⊗c Γ₀ Γ₁ cJ cJ' (⊗l⋆ S Γ f) ≗ ⊗l⋆ S Γ (⊗c (Γ ++ Γ₀) Γ₁ cJ cJ' f)
⊗c⊗l⋆ (just x) [] Γ₀ Γ₁ = refl
⊗c⊗l⋆ (just x) (x₁ ∷ Γ) Γ₀ Γ₁ = 
  ⊗c⊗l⋆ (just (x ⊗ x₁)) Γ Γ₀ Γ₁
  ∙ cong⊗l⋆ {just (x ⊗ x₁)} {Γ} (~ ⊗l⊗c {Γ = Γ ++ Γ₀})
⊗c⊗l⋆ nothing [] Γ₀ Γ₁ = ~ Il⊗c
⊗c⊗l⋆ nothing (x ∷ Γ) Γ₀ Γ₁ = 
  ⊗c⊗l⋆ (just (I ⊗ x)) Γ Γ₀ Γ₁
  ∙ cong⊗l⋆ {just (I ⊗ x)} {Γ}
      (~ ⊗l⊗c {Γ = Γ ++ Γ₀}
       ∙ ⊗l (~ Il⊗c))

-- ==========================================================================

-- An admissible rule, merging together Ic and ⊗c. This allows to
-- directly remove closed formulae from the passive context. Also,
-- some of its laws.

Jc : {S : Stp}(Γ₀ Γ₁ : Cxt){C J : Fma}(cJ : isCl J)
    → (f : S ∣ Γ₀ ++ Γ₁ ⊢ C)
    → S ∣ Γ₀ ++ J ∷ Γ₁ ⊢ C
Jc Γ₀ Γ₁ isI f = Ic Γ₀ Γ₁ f
Jc Γ₀ Γ₁ (is⊗ cJ cJ₁) f = ⊗c Γ₀ Γ₁ cJ cJ₁ (Jc Γ₀ (_ ∷ Γ₁) cJ (Jc Γ₀ Γ₁ cJ₁ f))

congJc : ∀{S} Γ Δ {C J} (cJ : isCl J)
    → {f g : S ∣ Γ ++ Δ ⊢ C}
    → f ≗ g → Jc Γ Δ cJ f ≗ Jc Γ Δ cJ g
congJc Γ Δ isI p = Ic Γ Δ p
congJc Γ Δ (is⊗ cJ cJ₁) p =
  ⊗c Γ Δ cJ cJ₁ (congJc Γ (_ ∷ Δ) cJ (congJc Γ Δ cJ₁ p))

letJ : {T S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {C J : Fma} (cJ : isCl J)
  → T ∣ Γ ⊢ J →  S ∣ Δ₀ ++ Δ₁ ⊢ C
  → S ∣ Δ₀ ++ asCxt T Γ ++ Δ₁ ⊢ C
letJ Γ Δ isI f g = letI Γ Δ f g
letJ Γ Δ (is⊗ cJ cJ') f g = let⊗ Γ Δ cJ cJ' f (Jc Γ (_ ∷ Δ) cJ (Jc Γ Δ cJ' g))

letJ-ax : {S : Stp} →  (Δ₀ Δ₁ : Cxt) → {C J : Fma} (cJ : isCl J)
  → (g : S ∣ Δ₀ ++ Δ₁ ⊢ C)
  → letJ Δ₀ Δ₁ cJ ax g ≡ Jc Δ₀ Δ₁ cJ g
letJ-ax Δ₀ Δ₁ isI g = refl
letJ-ax Δ₀ Δ₁ (is⊗ cJ cJ₁) g = refl

letJ-uf : {S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {A C J : Fma} (cJ : isCl J)
  → (f : just A ∣ Γ ⊢ J) → (g : S ∣ Δ₀ ++ Δ₁ ⊢ C)
  → letJ Δ₀ Δ₁ cJ (uf f) g ≡ letJ Δ₀ Δ₁ cJ f g
letJ-uf Δ₀ Δ₁ isI f g = refl
letJ-uf Δ₀ Δ₁ (is⊗ cJ cJ₁) f g = refl

letJ-⊗l : {S : Stp} → {Γ : Cxt} (Δ₀ Δ₁ : Cxt) → {A B C J : Fma} (cJ : isCl J)
  → (f : just A ∣ B ∷ Γ ⊢ J) → (g : S ∣ Δ₀ ++ Δ₁ ⊢ C)
  → letJ Δ₀ Δ₁ cJ (⊗l f) g ≡ ⊗c Δ₀ (Γ ++ Δ₁) (isCl-stp cJ f) (isCl-cxt [] cJ f refl) (letJ Δ₀ Δ₁ cJ f g)
letJ-⊗l Δ₀ Δ₁ isI f g = refl
letJ-⊗l Δ₀ Δ₁ (is⊗ cJ cJ₁) f g = refl

letJ-Jc : {T S : Stp} → {Γ₁ Γ₂ : Cxt} (Δ₀ Δ₁ : Cxt) → {C J K : Fma} (cJ : isCl J) (cK : isCl K)
  → (f : T ∣ Γ₁ ++ Γ₂ ⊢ J) → (g : S ∣ Δ₀ ++ Δ₁ ⊢ C)
  → letJ Δ₀ Δ₁ cJ (Jc Γ₁ Γ₂ cK f) g ≗ Jc (Δ₀ ++ asCxt T Γ₁) (Γ₂ ++ Δ₁) cK (letJ Δ₀ Δ₁ cJ f g)
letJ-Jc Δ₀ Δ₁ isI isI f g = refl
letJ-Jc Δ₀ Δ₁ (is⊗ cJ cJ₁) isI f g = refl
letJ-Jc {T} {Γ₁ = Γ₁} {Γ₂} Δ₀ Δ₁ isI (is⊗ cK cK₁) f g =
  ⊗c (Δ₀ ++ asCxt T Γ₁) (Γ₂ ++ Δ₁) cK cK₁
    (letJ-Jc Δ₀ Δ₁ isI cK (Jc Γ₁ Γ₂ cK₁ f) g
    ∙ congJc (Δ₀ ++ asCxt T Γ₁) (_ ∷ Γ₂ ++ Δ₁) cK (letJ-Jc Δ₀ Δ₁ isI cK₁ f g))
letJ-Jc {T} {Γ₁ = Γ₁} {Γ₂} Δ₀ Δ₁ (is⊗ cJ cJ₁) (is⊗ cK cK₁) f g =
  ⊗c (Δ₀ ++ asCxt T Γ₁) (Γ₂ ++ Δ₁) cK cK₁
    (letJ-Jc Δ₀ Δ₁ (is⊗ cJ cJ₁) cK (Jc Γ₁ Γ₂ cK₁ f) g
    ∙ congJc (Δ₀ ++ asCxt T Γ₁) (_ ∷ Γ₂ ++ Δ₁) cK (letJ-Jc Δ₀ Δ₁ (is⊗ cJ cJ₁) cK₁ f g))

ccut-Jc2 : {S T : Stp} → {Γ : Cxt} → (Δ₀ Δ' : Cxt) → {C J : Fma} (cJ : isCl J) → 
               (f : S ∣ Γ ⊢ J)(g : T ∣ Δ₀ ++ Δ' ⊢ C) →
              ccut Δ₀ f (Jc Δ₀ Δ' cJ g) refl ≗ letJ Δ₀ Δ' cJ f g
ccut-Jc2 Δ₀ Δ' isI f g rewrite cases++-inj₂ [] Δ₀ Δ' I = refl
ccut-Jc2 Δ₀ Δ' (is⊗ {J}{J'} cJ cJ₁) f g rewrite cases++-inj₂ [] Δ₀ Δ' (J ⊗ J') = refl

Jr : {J : Fma} (cJ : isCl J) → nothing ∣ [] ⊢ J
Jr isI = Ir
Jr (is⊗ cJ cJ₁) = ⊗r (Jr cJ) (Jr cJ₁)

cmplt-ρJ : {A J : Fma} (cJ : isCl J)
  → cmplt (ρJ {A} cJ) ≗ ⊗r ax (Jr cJ)
cmplt-ρJ isI = refl
cmplt-ρJ (is⊗ cJ cJ') =
  cong-scut (cmplt-ρJ cJ) (⊗l (⊗r refl (uf (cmplt-ρJ cJ'))))
  ∙ ⊗r refl (scut⊗r (Jr cJ) ax _ ∙ ⊗r (≡-to-≗ (scut-unit (Jr cJ))) refl)


ufJc2 : {Γ Δ : Cxt} {A C J : Fma}
  → {cJ : isCl J}
  → {f : just A ∣ Γ ++ Δ ⊢ C}
  → uf (Jc Γ Δ cJ f) ≗ Jc (A ∷ Γ) Δ cJ (uf f)
ufJc2 {cJ = isI} = ufIc2
ufJc2 {Γ}{Δ} {cJ = is⊗ cJ cJ₁} =
  uf⊗c2
  ∙ ⊗c (_ ∷ Γ) Δ cJ cJ₁
      (ufJc2 {Γ}{_ ∷ Δ}{cJ = cJ}
      ∙ congJc (_ ∷ Γ) (_ ∷ Δ) cJ (ufJc2 {cJ = cJ₁}))

⊗rJc1 : {S : Stp}{Γ Γ' Δ : Cxt}{A B J : Fma}
    → {cJ : isCl J}
    → {f : S ∣ Γ ++ Γ' ⊢ A} {g : nothing ∣ Δ ⊢ B}
    → ⊗r (Jc Γ Γ' cJ f) g ≗ Jc Γ (Γ' ++ Δ) cJ (⊗r f g)
⊗rJc1 {cJ = isI} = ⊗rIc1
⊗rJc1 {_}{Γ}{Γ'}{Δ}{cJ = is⊗ cJ cJ₁} =
  ⊗r⊗c1
  ∙ ⊗c Γ (Γ' ++ Δ) cJ cJ₁
      (⊗rJc1 {_}{Γ}{_ ∷ Γ'}{Δ}{cJ = cJ}
      ∙ congJc Γ (_ ∷ Γ' ++ Δ) cJ (⊗rJc1 {cJ = cJ₁}))

⊗rJc2 : {S : Stp}{Γ Δ Δ' : Cxt}{A B J : Fma}
    → {cJ : isCl J}
    → {f : S ∣ Γ ⊢ A} {g : nothing ∣ Δ ++ Δ' ⊢ B}
    → ⊗r f (Jc Δ Δ' cJ g) ≗ Jc (Γ ++ Δ) Δ' cJ (⊗r f g)
⊗rJc2 {cJ = isI} = ⊗rIc2
⊗rJc2 {Γ = Γ} {Δ} {Δ'} {cJ = is⊗ cJ cJ₁} =
  ⊗r⊗c2
  ∙ ⊗c (Γ ++ Δ) Δ' cJ cJ₁
      (⊗rJc2 {_}{Γ}{Δ}{_ ∷ Δ'} {cJ = cJ}
      ∙ congJc (Γ ++ Δ) (_ ∷ Δ') cJ (⊗rJc2 {cJ = cJ₁}))

⊗cJc : {S : Stp} {Γ Δ Λ : Cxt} {C J K K' : Fma}
    → {cJ : isCl J} {cK : isCl K} {cK' : isCl K'}
    → {f : S ∣ Γ ++ K ∷ K' ∷ Δ ++ Λ ⊢ C}
    → ⊗c Γ (Δ ++ J ∷ Λ) cK cK' (Jc (Γ ++ K ∷ K' ∷ Δ) Λ cJ f)
          ≗ Jc (Γ ++ K ⊗ K' ∷ Δ) Λ cJ (⊗c Γ (Δ ++ Λ) cK cK' f)
⊗cJc {Γ = Γ} {Δ} {Λ} {cJ = isI} = ⊗cIc
⊗cJc {Γ = Γ} {Δ} {Λ} {cJ = is⊗ cJ cJ₁} =
  ⊗c⊗c ∙ ⊗c (Γ ++ _ ∷ Δ) Λ _ _ (⊗cJc ∙ congJc (Γ ++ _ ∷ Δ) (_ ∷ Λ) cJ ⊗cJc)

JcJc : {S : Stp} {Γ Δ Λ : Cxt} {C J K : Fma}
    → {cJ : isCl J} {cK : isCl K}
    → {f : S ∣ Γ ++ Δ ++ Λ ⊢ C}
    → Jc Γ (Δ ++ K ∷ Λ) cJ (Jc (Γ ++ Δ) Λ cK f)
          ≗ Jc (Γ ++ J ∷ Δ) Λ cK (Jc Γ (Δ ++ Λ) cJ f)
JcJc {cJ = isI} {isI} = IcIc
JcJc {Γ = Γ} {Δ} {Λ} {cJ = isI} {is⊗ cK cK₁} =
  Ic⊗c
  ∙ ⊗c (Γ ++ I ∷ Δ) Λ cK cK₁
       (JcJc {Γ = Γ}{Δ}{_ ∷ Λ} {cJ = isI}{cK}
       ∙ congJc (Γ ++ I ∷ Δ) (_ ∷ Λ) cK (JcJc {cJ = isI}{cK₁}))
JcJc {Γ = Γ}{Δ}{Λ}{cJ = is⊗ cJ cJ₁} {isI} =
  ⊗c Γ (Δ ++ I ∷ Λ) cJ cJ₁
      (congJc Γ (_ ∷ Δ ++ I ∷ Λ) cJ (JcJc {Γ = Γ}{Δ}{Λ}{cJ = cJ₁}{isI})
      ∙ JcJc {Γ = Γ}{_ ∷ Δ}{Λ}{cJ = cJ}{isI})
  ∙ ⊗cIc
JcJc {Γ = Γ}{Δ}{Λ}{cJ = is⊗ cJ cJ₁} {is⊗ cK cK₁} =
  ⊗c Γ (Δ ++ _ ∷ Λ) cJ cJ₁
      (congJc Γ (_ ∷ Δ ++ _ ∷ Λ) cJ (JcJc {Γ = Γ}{Δ}{Λ}{cJ = cJ₁}{is⊗ cK cK₁})
      ∙ JcJc {Γ = Γ}{_ ∷ Δ}{Λ}{cJ = cJ}{is⊗ cK cK₁})
  ∙ ⊗c⊗c
  ∙ ⊗c (Γ ++ _ ∷ Δ) Λ cK cK₁
       (⊗cJc {Γ = Γ}{Δ}{_ ∷ Λ}
        ∙ congJc (Γ ++ _ ∷ Δ) (_ ∷ Λ) cK ⊗cJc)


JcJr : {J : Fma}(cJ : isCl J)
    → Jc [] [] cJ (Jr cJ) ≗ uf ax
JcJr isI =
  ~ ufIc1
  ∙ uf (~ axI)
JcJr (is⊗ cJ cJ₁) =
  ⊗c [] [] cJ cJ₁
    (congJc [] (_ ∷ []) cJ ((~ ⊗rJc2) ∙ ⊗r refl (JcJr cJ₁))
     ∙ (~ ⊗rJc1)
     ∙ ⊗r (JcJr cJ) refl
     ∙ ⊗ruf)
  ∙ ~ uf⊗c1
  ∙ uf (~ ax⊗)

-- Non-determinism of type (i) (as we call it in the paper) vanishes.

non-det : ∀{S Γ C J}(cJ : isCl J)(f : S ∣ Γ ⊢ C)
  → Jc Γ [] cJ (⊗r f (Jr cJ)) ≗ ⊗r f (uf ax)
non-det isI f =
  (~ ⊗rIc2)
  ∙ ⊗r refl ((~ ufIc1) ∙ uf (~ axI)) 
non-det {Γ = Γ} (is⊗ cJ cJ') f =
  ⊗c Γ [] cJ cJ'
      (JcJc {Γ = Γ}{[]}
       ∙ congJc (Γ ++ _ ∷ []) [] cJ' (~ ⊗rJc2)
       ∙ (~ ⊗rJc2)
       ∙ ⊗r refl
            (congJc (_ ∷ []) [] cJ' (~ ⊗rJc1 ∙ ⊗r (JcJr cJ) refl ∙ ⊗ruf)
             ∙ (~ ufJc2)
             ∙ uf (non-det cJ' ax)))
  ∙ (~ ⊗r⊗c2)
  ∙ ⊗r refl ((~ uf⊗c1 {cJ = cJ}{cJ'} ) ∙ uf (~ ax⊗))

-- ======================================================================

-- Completeness map applied to ρJ-1

cmplt-ρJ-1 : {A J : Fma} (cJ : isCl J)
  → cmplt (ρJ-1 {A} cJ) ≗ ⊗l (Jc [] [] cJ ax)
cmplt-ρJ-1 isI = refl
cmplt-ρJ-1 (is⊗ cJ cJ') = 
  ⊗l
    (cong-scut (⊗r refl (uf (cmplt-ρJ-1 cJ'))) (cmplt-ρJ-1 cJ)
     ∙ ccut-Jc2 [] [] cJ (uf (⊗l (Jc [] [] cJ' ax))) ax
     ∙ lem)
  where
    lem : letJ [] [] cJ (uf (⊗l (Jc [] [] cJ' ax))) ax ≗
      ⊗c [] [] cJ cJ' (Jc [] (_ ∷ []) cJ (Jc [] [] cJ' ax))
    lem =
      proof≗ 
        letJ [] [] cJ (uf (⊗l (Jc [] [] cJ' ax))) ax
      ≗〈 ≡-to-≗ (letJ-uf [] [] cJ _ _) 〉 
        letJ [] [] cJ (⊗l (Jc [] [] cJ' ax)) ax
      ≗〈 ≡-to-≗ (letJ-⊗l [] [] cJ _ _) 〉 
        ⊗c [] [] _ _ (letJ [] [] cJ (Jc [] [] cJ' ax) ax)
      ≗〈 ≡-to-≗ (cong₂ (λ x y → ⊗c [] [] x y (letJ [] [] cJ (Jc [] [] cJ' ax) ax)) (uniq-cl _ _) (uniq-cl _ _)) 〉 
        ⊗c [] [] cJ cJ' (letJ [] [] cJ (Jc [] [] cJ' ax) ax)
      ≗〈 ⊗c [] [] _ _ (letJ-Jc [] [] cJ cJ' ax ax) 〉 
        ⊗c [] [] cJ cJ' (Jc (_ ∷ []) [] cJ' (letJ [] [] cJ ax ax))
      ≗〈 ⊗c [] [] _ _ (≡-to-≗ (cong (Jc (_ ∷ []) [] cJ') (letJ-ax [] [] cJ ax))) 〉 
        ⊗c [] [] cJ cJ' (Jc (_ ∷ []) [] cJ' (Jc [] [] cJ ax))
      ≗〈 ⊗c [] [] cJ cJ' (~ JcJc) 〉 
        ⊗c [] [] cJ cJ' (Jc [] (_ ∷ []) cJ (Jc [] [] cJ' ax))
      qed≗

-- ======================================================================

-- Completeness map applied to αJ-1

cmplt-αJ-1 : {A J J' : Fma} (cJ : isCl J)(cJ' : isCl J')
  → cmplt (αJ-1 {A}{J} cJ') ≗ ⊗l (⊗c [] [] cJ cJ' (⊗r (⊗r ax (uf ax)) (uf ax)))
cmplt-αJ-1 cJ cJ' =
  ⊗l (cong-scut2 (⊗r ax (uf (cmplt (ρJ-1 cJ')))) (cmplt-ρJ cJ')
     ∙ ⊗r (⊗r refl (uf (cmplt-ρJ-1 cJ'))) refl
     ∙ lem)
  where
    lem : ⊗r (⊗r ax (uf (⊗l (Jc [] [] cJ' ax)))) (Jr cJ') ≗
      ⊗c [] [] cJ cJ' (⊗r (⊗r ax (uf ax)) (uf ax))
    lem =
      proof≗
        ⊗r (⊗r ax (uf (⊗l (Jc [] [] cJ' ax)))) (Jr cJ')
      ≗〈 ⊗r (⊗r refl uf⊗c1) refl  〉 
        ⊗r (⊗r ax (⊗c [] [] cJ cJ' (uf (Jc [] [] cJ' ax)))) (Jr cJ')
      ≗〈 ⊗r (⊗r refl (⊗c [] [] cJ cJ' ufJc2)) refl 〉 
        ⊗r (⊗r ax (⊗c [] [] cJ cJ' (Jc (_ ∷ []) [] cJ' (uf ax)))) (Jr cJ')
      ≗〈 ⊗r ⊗r⊗c2 refl 〉 
        ⊗r (⊗c [] [] cJ cJ' (⊗r ax (Jc (_ ∷ []) [] cJ' (uf ax)))) (Jr cJ')
      ≗〈 ⊗r (⊗c [] [] cJ cJ' ⊗rJc2) refl 〉 
        ⊗r (⊗c [] [] cJ cJ' (Jc (_ ∷ []) [] cJ' (⊗r ax (uf ax)))) (Jr cJ')
      ≗〈 ⊗r⊗c1 〉 
        ⊗c [] [] cJ cJ' (⊗r (Jc (_ ∷ []) [] cJ' (⊗r ax (uf ax))) (Jr cJ'))
      ≗〈 ⊗c [] [] cJ cJ' ⊗rJc1 〉 
        ⊗c [] [] cJ cJ' (Jc (_ ∷ []) [] cJ' (⊗r (⊗r ax (uf ax)) (Jr cJ')))
      ≗〈 ⊗c [] [] cJ cJ' (non-det cJ' (⊗r ax (uf ax))) 〉 
        ⊗c [] [] cJ cJ' (⊗r (⊗r ax (uf ax)) (uf ax))
      qed≗

-- -- this is the main result needed to prove that strcmplt is left
-- -- inverse of sound up to ≗, which we prove in the file
-- -- StrongComplete.agda

⊗l⋆++ : (S : Stp) → (Γ₁ Γ₂ : Cxt) → {Δ : Cxt}{C : Fma} {f : S ∣ Γ₁ ++ Γ₂ ++ Δ ⊢ C}
  → ⊗l⋆ S (Γ₁ ++ Γ₂) {Δ} f ≡ ⊗l⋆ (just [ t S ∣ Γ₁ ]) Γ₂ (⊗l⋆ S Γ₁ {Γ₂ ++ Δ} f)
⊗l⋆++ (just A) [] Γ₂ = refl
⊗l⋆++ (just A) (B ∷ Γ₁) Γ₂ = ⊗l⋆++ (just (A ⊗ B)) Γ₁ Γ₂
⊗l⋆++ nothing [] [] = refl
⊗l⋆++ nothing [] (B ∷ Γ₂) = refl
⊗l⋆++ nothing (B ∷ Γ₁) Γ₂ = ⊗l⋆++ (just (I ⊗ B)) Γ₁ Γ₂

-- the function cmplt ∘ sound is ≗-related to ⊗l⋆

cmpltsound' : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢ C) → cmplt (sound f) ≗ ⊗l⋆ S Γ f
cmpltsound' ax = refl
cmpltsound' (uf {Γ}{A} f) =
  proof≗
  scut (cmplt [ l ∣ Γ ]f) (cmplt (sound f))
  ≗〈 cong-scut2 (cmplt [ l ∣ Γ ]f) (cmpltsound' f) 〉
  scut (cmplt [ l ∣ Γ ]f) (⊗l⋆ (just A) Γ f)
  ≗〈 cong-scut1 (cmplt-uf-lemma Γ l) 〉
  scut (⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ ax))))) (⊗l⋆ (just A) Γ f)
  ≗〈 ≡-to-≗ (scut⊗l⋆ {just (I ⊗ A)}{Γ})  〉
  ⊗l⋆ (just (I ⊗ A)) Γ (scut (⊗l (Il (uf (⊗l-1⋆ (just A) Γ ax)))) (⊗l⋆ (just A) Γ {[]} f))
  ≗〈 refl 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (scut (⊗l-1⋆ (just A) Γ ax) (⊗l⋆ (just A) Γ {[]} f)))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (scut⊗l-1⋆ {just A}{Γ}))))) 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ (scut ax (⊗l⋆ (just A) Γ {[]} f))))))
  ≗〈 refl 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ (⊗l⋆ (just A) Γ {[]} f)))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (⊗l⋆-iso {just A}{Γ}))))) 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf f)))
  qed≗
cmpltsound' Ir = axI
cmpltsound' (⊗r {S}{Γ}{Δ} f f') = 
  proof≗
  scut (cmplt (φ S Γ Δ)) (⊗l (⊗r (cmplt (sound f)) (uf (cmplt (sound f')))))
  ≗〈 cong-scut2 (cmplt (φ S Γ Δ)) (⊗l (⊗r (cmpltsound' f) (uf (cmpltsound' f')))) 〉
  scut (cmplt (φ S Γ Δ)) (⊗l (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f'))))
  ≗〈 cong-scut1 (cmplt-⊗r-lemma {S}{Γ}{Δ}) 〉
  scut (⊗l⋆ S (Γ ++ Δ) (⊗r (⊗l-1⋆ S Γ ax) (⊗l-1⋆ nothing Δ ax))) (⊗l (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f'))))
  ≗〈 ≡-to-≗ (scut⊗l⋆ {S}{Γ ++ Δ}) 〉
  ⊗l⋆ S (Γ ++ Δ) (scut (⊗l-1⋆ S Γ ax) (⊗r (⊗l⋆ S Γ {[]} f) (scut (⊗l-1⋆ nothing Δ ax) (⊗l⋆ nothing Δ {[]} f')))) 
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (cong-scut2 (⊗l-1⋆ S Γ ax) (⊗r refl (≡-to-≗ (scut⊗l-1⋆ {nothing}{Δ})))) 〉
  ⊗l⋆ S (Γ ++ Δ) (scut (⊗l-1⋆ S Γ ax) (⊗r (⊗l⋆ S Γ {[]} f) (⊗l-1⋆ nothing Δ (⊗l⋆ nothing Δ {[]} f'))))
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (cong-scut2 (⊗l-1⋆ S Γ ax) (⊗r refl (≡-to-≗ (⊗l⋆-iso {nothing}{Δ})))) 〉
  ⊗l⋆ S (Γ ++ Δ) (scut (⊗l-1⋆ S Γ ax) (⊗r (⊗l⋆ S Γ {[]} f) f'))
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (≡-to-≗ (scut⊗l-1⋆ {S}{Γ})) 〉
  ⊗l⋆ S (Γ ++ Δ) (⊗l-1⋆ S Γ (⊗r (⊗l⋆ S Γ {[]} f) f'))
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (cong⊗l-1⋆ {S} {Γ} (⊗r⊗l⋆ {S}{Γ})) 〉
  ⊗l⋆ S (Γ ++ Δ) (⊗l-1⋆ S Γ (⊗l⋆ S Γ {Δ} (⊗r f f')))
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (≡-to-≗ (⊗l⋆-iso {S}{Γ})) 〉
  ⊗l⋆ S (Γ ++ Δ) {[]} (⊗r f f')
  qed≗
cmpltsound' (Il {Γ = []} f) = cmpltsound' f
cmpltsound' (Il {Γ = _ ∷ _} f) = cmpltsound' f
cmpltsound' (⊗l f) = cmpltsound' f
cmpltsound' {S} (Ic Γ Δ f) =
  cong-scut (cmplt-uf-lemma Δ ρ-1) (cmpltsound' f)
  ∙ ≡-to-≗ (scut⊗l⋆ {just ([ t S ∣ Γ ] ⊗ I)} {Δ})
  ∙ cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ I)} {Δ}
      (⊗l (Ic [] Δ (≡-to-≗ (trans (scut⊗l-1⋆ {just [ t S ∣ Γ ]} {Δ})
                                  (trans (cong (⊗l-1⋆ (just [ t S ∣ Γ ]) Δ {[]}) (⊗l⋆++ S Γ Δ))
                                         (⊗l⋆-iso {just [ t S ∣ Γ ]}{Δ}))))
          ∙ Ic⊗l⋆ S Γ [] Δ {f = f}))
  ∙ ≡-to-≗
      (sym (trans (⊗l⋆++ S (Γ ++ I ∷ []) Δ {[]})
                  (cong (⊗l⋆ (just ([ t S ∣ Γ ] ⊗ I)) Δ) (⊗l⋆++ S Γ (I ∷ [])))))
cmpltsound' {S} (⊗c Γ Δ {J = J}{J'} cJ cJ' f) = 
  cong-scut (cmplt-uf-lemma Δ (αJ-1 _)) (cmpltsound' f)
  ∙ cong-scut1 (cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ _)}{Δ} (cong-scut1 (cmplt-αJ-1 cJ cJ')))  --≡-to-≗ (scut⊗l⋆ {just ([ t S ∣ Γ ] ⊗ _)} {Δ})
  ∙ ≡-to-≗ (scut⊗l⋆ {just ([ t S ∣ Γ ] ⊗ _)} {Δ})
  ∙ lem
  where
    lem :
      ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ
        (⊗l
          (⊗c [] Δ cJ cJ'
            (scut
              (scut (⊗r (⊗r ax (uf ax)) (uf ax))
              (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} ax))
            (⊗l⋆ S (Γ ++ J ∷ J' ∷ Δ) {[]} f))))
        ≗ ⊗l⋆ S (Γ ++ J ⊗ J' ∷ Δ) (⊗c Γ Δ cJ cJ' f)
    lem =
      proof≗ 
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ cJ cJ' (scut (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} ax)) (⊗l⋆ S (Γ ++ J ∷ J' ∷ Δ) {[]} f))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ _ _ (~ (scut-ass-scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} ax) _)))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ cJ cJ' (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (scut (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} ax) (⊗l⋆ S (Γ ++ J ∷ J' ∷ Δ) {[]} f)))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ _ _ (cong-scut2 (⊗r (⊗r ax (uf ax)) (uf ax)) (≡-to-≗ (scut⊗l-1⋆ {just ([ t S ∣ Γ ] ⊗ J ⊗ J')}{Δ}{[]}))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ cJ cJ' (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ (⊗l⋆ S (Γ ++ J ∷ J' ∷ Δ) {[]} f)))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ _ _ (cong-scut2 (⊗r (⊗r ax (uf ax)) (uf ax)) (cong⊗l-1⋆ {just ([ t S ∣ Γ ] ⊗ J ⊗ J')}{Δ} {[]}
         (≡-to-≗ (⊗l⋆++ S (Γ ++ J ∷ J' ∷ []) Δ)))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ cJ cJ'
          (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} (⊗l⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ (⊗l⋆ S (Γ ++ J ∷ J' ∷ []) {Δ} f ))))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ _ _ (cong-scut2 (⊗r (⊗r ax (uf ax)) (uf ax)) (≡-to-≗ (⊗l⋆-iso {just ([ t S ∣ Γ ] ⊗ J ⊗ J')}{Δ} {[]}))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ cJ cJ' (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l⋆ S (Γ ++ J ∷ J' ∷ []) {Δ} f ))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ _ _ (cong-scut2 (⊗r (⊗r ax (uf ax)) (uf ax)) (≡-to-≗ (⊗l⋆++ S Γ (J ∷ J' ∷ []) {Δ}))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ cJ cJ' (ccut [] (uf ax) (ccut (J ∷ []) (uf ax) (⊗l⋆ S Γ f) refl) refl)))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ _ _ (≡-to-≗ (trans (ccut-unit [] (ccut (J ∷ []) (uf ax) (⊗l⋆ S Γ f) refl) refl) (ccut-unit (J ∷ []) (⊗l⋆ S Γ f) refl))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ cJ cJ' (⊗l⋆ S Γ f)))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c⊗l⋆ S Γ [] Δ)) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗l⋆ S Γ (⊗c Γ Δ cJ cJ' f)))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (≡-to-≗ (sym (⊗l⋆++ S Γ (J ⊗ J' ∷ []) {Δ}))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l⋆ S (Γ ++ J ⊗ J' ∷ []) (⊗c Γ Δ cJ cJ' f))
      ≗〈 ≡-to-≗ (sym (⊗l⋆++ S (Γ ++ J ⊗ J' ∷ []) Δ)) 〉
        ⊗l⋆ S (Γ ++ J ⊗ J' ∷ Δ) (⊗c Γ Δ cJ cJ' f)
      qed≗

cmpltsound : {A B : Fma} → (f : just A ∣ [] ⊢ B) → cmplt (sound f) ≗ f
cmpltsound = cmpltsound'

-- ====================================================================



-- strcmplt is left inverse of sound

strcmpltsound : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢ C) →
                 strcmplt (sound f) ≗ f
strcmpltsound {S}{Γ} f =
  proof≗
  strcmplt (sound f)
  ≗〈 cong⊗l-1⋆ {S}{Γ} (cmpltsound' f) 〉
  ⊗l-1⋆ S Γ (⊗l⋆ S Γ f)
  ≗〈 ≡-to-≗ ⊗l⋆-iso 〉
  f
  qed≗

-- ====================================================================

-- sound ∘ ⊗l-1⋆ is equal to sound

soundIl-1 : {Γ : Cxt}{C : Fma}{f : just I ∣ Γ ⊢ C}
  → sound (Il-1 f) ≐ sound f
soundIl-1 {f = ax} = refl
soundIl-1 {f = ⊗r f g} = soundIl-1 {f = f} ⊗ refl ∘ refl
soundIl-1 {f = Il f} = refl
soundIl-1 {f = Ic Γ Δ f} = soundIl-1 {f = f} ∘ refl
soundIl-1 {f = ⊗c Γ Δ cJ cJ' f} = soundIl-1 {f = f} ∘ refl

sound⊗l-1 : {Γ : Cxt}{A B C : Fma}{f : just (A ⊗ B) ∣ Γ ⊢ C}
  → sound (⊗l-1 f) ≐ sound f
sound⊗l-1 {f = ax} = 
  proof≐
  id ⊗ (id ∘ l) ∘ ((id ∘ α) ∘ (ρ ⊗ id))
  ≐⟨ refl ⊗ lid ∘ (lid ∘ refl) ⟩
  id ⊗ l ∘ (α ∘ ρ ⊗ id)
  ≐⟨ ~ ass ⟩
  id ⊗ l ∘ α ∘ ρ ⊗ id
  ≐⟨ ~ lαρ ⟩
  id
  qed≐
sound⊗l-1 {f = ⊗r f g} = sound⊗l-1 {f = f} ⊗ refl ∘ refl
sound⊗l-1 {f = ⊗l f} = refl
sound⊗l-1 {f = Ic Γ Δ f} = sound⊗l-1 {f = f} ∘ refl
sound⊗l-1 {f = ⊗c Γ Δ cJ cJ' f} = sound⊗l-1 {f = f} ∘ refl

sound⊗l-1⋆ : {S : Stp}{Γ : Cxt}{C : Fma}{f : just 〈 S ∣ Γ 〉 ∣ [] ⊢ C}
  → sound (⊗l-1⋆ S Γ f) ≐ sound f
sound⊗l-1⋆ {just A} {[]} = refl
sound⊗l-1⋆ {just A} {B ∷ Γ} {f = f} =
  proof≐
  sound (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f))
  ≐⟨ sound⊗l-1 {f = ⊗l-1⋆ (just (A ⊗ B)) Γ f} ⟩
  sound (⊗l-1⋆ (just (A ⊗ B)) Γ f)
  ≐⟨ sound⊗l-1⋆ {S = just (A ⊗ B)}{Γ} ⟩
  sound f
  qed≐
sound⊗l-1⋆ {nothing} {[]}{f = f} = soundIl-1 {f = f}
sound⊗l-1⋆ {nothing} {B ∷ Γ}{f = f} =
  proof≐
  sound (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)))
  ≐⟨ soundIl-1 {f = ⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)} ⟩
  sound (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))
  ≐⟨ sound⊗l-1 {f = ⊗l-1⋆ (just (I ⊗ B)) Γ f} ⟩
  sound (⊗l-1⋆ (just (I ⊗ B)) Γ f)
  ≐⟨ sound⊗l-1⋆ {just (I ⊗ B)}{Γ} ⟩
  sound f
  qed≐

-- ====================================================================

-- sound is left inverse of strcmplt

soundstrcmplt : {S : Stp}{Γ : Cxt}{C : Fma}(f : 〈 S ∣ Γ 〉 ⇒ C) →
           sound (strcmplt {S}{Γ} f) ≐ f 
soundstrcmplt {S}{Γ} f =
  proof≐ 
  sound (strcmplt {S}{Γ} f)
  ≐⟨ sound⊗l-1⋆ {S}{Γ} ⟩
  sound (cmplt f)
  ≐⟨ soundcmplt f ⟩
  f
  qed≐
