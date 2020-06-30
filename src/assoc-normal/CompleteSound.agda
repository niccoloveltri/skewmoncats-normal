{-# OPTIONS --rewriting #-}

module CompleteSound where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.Bool
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk
open import Cuts
open import MulticatLaws1
open import MulticatLaws2
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

-- ⊗c permutes with ⊗l⋆

⊗c⊗l⋆ : (S : Stp) (Γ Γ₀ Γ₁ : Cxt){C J J' : Fma}
    → {f : S ∣ Γ ++ Γ₀ ++ J ∷ J' ∷ Γ₁ ⊢ C}
    → ⊗c Γ₀ Γ₁ (⊗l⋆ S Γ f) ≗ ⊗l⋆ S Γ (⊗c (Γ ++ Γ₀) Γ₁ f)
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
  ≗〈 cong-scut {f = cmplt [ l ∣ Γ ]f} refl (cmpltsound' f) 〉
  scut (cmplt [ l ∣ Γ ]f) (⊗l⋆ (just A) Γ f)
  ≗〈 cong-scut (cmplt-uf-lemma Γ l) refl 〉
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
  ≗〈 cong-scut {f = cmplt (φ S Γ Δ)} refl (⊗l (⊗r (cmpltsound' f) (uf (cmpltsound' f')))) 〉
  scut (cmplt (φ S Γ Δ)) (⊗l (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f'))))
  ≗〈 cong-scut (cmplt-⊗r-lemma {S}{Γ}{Δ}) refl 〉
  scut (⊗l⋆ S (Γ ++ Δ) (⊗r (⊗l-1⋆ S Γ ax) (⊗l-1⋆ nothing Δ ax))) (⊗l (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f'))))
  ≗〈 ≡-to-≗ (scut⊗l⋆ {S}{Γ ++ Δ}) 〉
  ⊗l⋆ S (Γ ++ Δ) (scut (⊗l-1⋆ S Γ ax) (⊗r (⊗l⋆ S Γ {[]} f) (scut (⊗l-1⋆ nothing Δ ax) (⊗l⋆ nothing Δ {[]} f')))) 
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (cong-scut {f = ⊗l-1⋆ S Γ ax} refl (⊗r refl (≡-to-≗ (scut⊗l-1⋆ {nothing}{Δ})))) 〉
  ⊗l⋆ S (Γ ++ Δ) (scut (⊗l-1⋆ S Γ ax) (⊗r (⊗l⋆ S Γ {[]} f) (⊗l-1⋆ nothing Δ (⊗l⋆ nothing Δ {[]} f'))))
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (cong-scut {f = ⊗l-1⋆ S Γ ax} refl (⊗r refl (≡-to-≗ (⊗l⋆-iso {nothing}{Δ})))) 〉
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
cmpltsound' {S} (⊗c Γ Δ {J = J}{J'} f) = 
  cong-scut (cmplt-uf-lemma Δ α-1) (cmpltsound' f)
  ∙ ≡-to-≗ (scut⊗l⋆ {just ([ t S ∣ Γ ] ⊗ _)} {Δ})
  ∙ lem
 where
   lem :
     ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ
       (⊗l
         (⊗c [] Δ 
           (scut
             (scut (⊗r (⊗r ax (uf ax)) (uf ax))
             (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} ax))
           (⊗l⋆ S (Γ ++ J ∷ J' ∷ Δ) {[]} f))))
       ≗ ⊗l⋆ S (Γ ++ J ⊗ J' ∷ Δ) (⊗c Γ Δ f)
   lem =
      proof≗ 
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ (scut (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} ax)) (⊗l⋆ S (Γ ++ J ∷ J' ∷ Δ) {[]} f))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ (~ (scut-ass-scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} ax) _)))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (scut (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} ax) (⊗l⋆ S (Γ ++ J ∷ J' ∷ Δ) {[]} f)))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ (cong-scut {f = ⊗r (⊗r ax (uf ax)) (uf ax)} refl (≡-to-≗ (scut⊗l-1⋆ {just ([ t S ∣ Γ ] ⊗ J ⊗ J')}{Δ}{[]}))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ (⊗l⋆ S (Γ ++ J ∷ J' ∷ Δ) {[]} f)))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ (cong-scut {f = ⊗r (⊗r ax (uf ax)) (uf ax)} refl (cong⊗l-1⋆ {just ([ t S ∣ Γ ] ⊗ J ⊗ J')}{Δ} {[]}
         (≡-to-≗ (⊗l⋆++ S (Γ ++ J ∷ J' ∷ []) Δ)))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ 
          (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ {[]} (⊗l⋆ (just ([ t S ∣ Γ ] ⊗ J ⊗ J')) Δ (⊗l⋆ S (Γ ++ J ∷ J' ∷ []) {Δ} f ))))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ (cong-scut {f = ⊗r (⊗r ax (uf ax)) (uf ax)} refl (≡-to-≗ (⊗l⋆-iso {just ([ t S ∣ Γ ] ⊗ J ⊗ J')}{Δ} {[]}))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l⋆ S (Γ ++ J ∷ J' ∷ []) {Δ} f ))))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ (cong-scut {f = ⊗r (⊗r ax (uf ax)) (uf ax)} refl (≡-to-≗ (⊗l⋆++ S Γ (J ∷ J' ∷ []) {Δ}))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ _)) --(ccut [] (uf ax) (ccut (J ∷ []) (uf ax) (⊗l⋆ S Γ f) refl) refl)))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c [] Δ (≡-to-≗ (trans (ccut-unit [] (ccut false (J ∷ []) (uf ax) (⊗l⋆ S Γ f) refl) refl) (ccut-unit (J ∷ []) (⊗l⋆ S Γ f) refl))))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗c [] Δ (⊗l⋆ S Γ f)))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (⊗l (⊗c⊗l⋆ S Γ [] Δ)) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l (⊗l⋆ S Γ (⊗c Γ Δ f)))
      ≗〈 cong⊗l⋆ {just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))} {Δ} {[]} (≡-to-≗ (sym (⊗l⋆++ S Γ (J ⊗ J' ∷ []) {Δ}))) 〉
        ⊗l⋆ (just ([ t S ∣ Γ ] ⊗ (J ⊗ J'))) Δ (⊗l⋆ S (Γ ++ J ⊗ J' ∷ []) (⊗c Γ Δ f))
      ≗〈 ≡-to-≗ (sym (⊗l⋆++ S (Γ ++ J ⊗ J' ∷ []) Δ)) 〉
        ⊗l⋆ S (Γ ++ J ⊗ J' ∷ Δ) (⊗c Γ Δ f)
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
soundIl-1 {f = ⊗c Γ Δ f} = soundIl-1 {f = f} ∘ refl

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
sound⊗l-1 {f = ⊗c Γ Δ f} = sound⊗l-1 {f = f} ∘ refl

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
