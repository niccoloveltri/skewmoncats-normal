{-# OPTIONS --rewriting #-}

module Sound where

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

-- interpretation of antecedents

-- -- (Note that an empty stoup contributes an I to the meaning 
-- -- of an antecedent.)

t : Stp → Fma
t nothing = I
t (just A) = A

[_∣_] : Fma → Cxt → Fma
[ A ∣ [] ] = A
[ A ∣ C ∷ Γ ] = [ A ⊗ C ∣ Γ ]

〈_∣_〉 : Stp → Cxt → Fma 
〈 S ∣ Γ 〉 = [ t S ∣ Γ ] 

-- ====================================================================

[_∣_]f : {A B : Fma} → A ⇒ B → (Γ : Cxt) → [ A ∣ Γ ] ⇒ [ B ∣ Γ ]
[ f ∣ [] ]f = f
[ f ∣ C ∷ Γ ]f = [ f ⊗ id ∣ Γ ]f

-- ====================================================================

ψ : (A B : Fma) → (Δ : Cxt) → 
                   [ A ⊗ B ∣  Δ ] ⇒ A ⊗ [ B ∣ Δ ] 
ψ A B [] = id
ψ A B (C ∷ Δ) = ψ A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f 

-- ====================================================================

[ass] : (A : Fma) → (Γ Δ : Cxt) → [ A ∣ Γ ++ Δ ] ≡ [ [ A ∣ Γ ] ∣ Δ ]
[ass] A [] Δ = refl
[ass] A (C ∷ Γ) Δ = [ass] (A ⊗ C) Γ Δ 

{-# REWRITE [ass] #-}

φ' : (A : Fma) → (Γ Δ : Cxt) →
                   [ A ∣ Γ ++ Δ ] ⇒ [ A ∣ Γ ] ⊗ [ I ∣ Δ ]
φ' A Γ Δ = ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f

φ : (S : Stp) → (Γ Δ : Cxt) →  
                   〈 S ∣ Γ ++ Δ 〉 ⇒ 〈 S ∣ Γ 〉 ⊗ 〈 nothing ∣ Δ 〉
φ S Γ Δ = φ' (t S) Γ Δ 

-- ====================================================================


[ass]f : {A B : Fma} → (f : A ⇒ B) → (Γ Δ : Cxt) → [ f ∣ Γ ++ Δ ]f ≡ [ [ f ∣ Γ ]f ∣ Δ ]f
[ass]f f [] Δ = refl
[ass]f f (x ∷ Γ) Δ = [ass]f (f ⊗ id) Γ Δ

{-# REWRITE [ass]f #-}

-- The soundness maps, interpreting focused derivations as categorical
-- derivations.

mutual
  sound : {S : Stp} {Γ : Cxt} {A : Fma} → S ∣ Γ ⊢L A → 〈 S ∣ Γ 〉 ⇒ A 
  sound (uf {Γ} f) = sound f ∘ [ l ∣ Γ ]f
  sound (Il f) = sound f
  sound (⊗l f) = sound f
  sound (switch-at f) = soundR f
  sound (switch-not f) = soundR f

  soundR : {S : StpR} {Γ : Cxt} {A : Fma} → S ∣ Γ ⊢R A → 〈 mmap ` S ∣ Γ 〉 ⇒ A 
  soundR ax = id
  soundR Ir = id
  soundR (⊗r {S} {Γ} {Δ} f g) = soundR f ⊗ sound g ∘ φ (mmap ` S) Γ Δ
  soundR (⊗r[] {Γ} f g) = soundR f ⊗ soundR g ∘ l-1

-- ====================================================================

-- Some extra valid equations, in particular several laws satisfied by
-- the auxiliary functions ψ and φ.


[≐∣_] : (Γ : Cxt) → {A B : Fma} → {f g : A ⇒ B} → 
                                     f ≐ g → [ f ∣ Γ ]f ≐ [ g ∣ Γ ]f
[≐∣ [] ] p = p
[≐∣ C ∷ Γ ] p = [≐∣ Γ ] (p ⊗ refl)

[id∣_] : (Γ : Cxt) → {A : Fma} → [ id {A} ∣ Γ ]f ≐ id {[ A ∣ Γ ]}
[id∣ [] ] = refl 
[id∣ C ∷ Γ ] = [≐∣ Γ ] f⊗id ∙ [id∣ Γ ]

[∘∣_] : (Γ : Cxt) → {A B C : Fma} → (f : B ⇒ C) → (g : A ⇒ B) → 
            [ f ∘ g ∣ Γ ]f ≐ [ f ∣ Γ ]f ∘ [ g ∣ Γ ]f
[∘∣ [] ] f g = refl
[∘∣ C ∷ Γ ] f g = 
   [≐∣ Γ ] (refl ⊗ rid ∙ f⊗∘) ∙ [∘∣ Γ ] (f ⊗ id) (g ⊗ id)


nψ : {A B C : Fma} → (Γ : Cxt) → (f : A ⇒ C) → 
            f ⊗ id ∘ ψ A B Γ ≐ ψ C B Γ ∘ [ f ⊗ id ∣ Γ ]f 
nψ [] f = ~ rid ∙ ~ lid
nψ (D ∷ Γ) f =
  proof≐
    f ⊗ id ∘ (ψ _ (_ ⊗ D) Γ ∘ [ α ∣ Γ ]f)
  ≐⟨ ~ ass ⟩ 
    f ⊗ id ∘ ψ _ (_ ⊗ D) Γ ∘ [ α ∣ Γ ]f
  ≐⟨ nψ Γ f ∘ refl ⟩ 
    ψ _ (_ ⊗ D) Γ ∘ [ f ⊗ id ∣ Γ ]f ∘ [ α ∣ Γ ]f
  ≐⟨ ass ∙ (refl ∘ (~ [∘∣ Γ ] _ _ ∙ [≐∣ Γ ] (refl ⊗ (~ f⊗id) ∘ refl))) ⟩ 
    ψ _ (_ ⊗ D) Γ ∘ [ f ⊗ (id ⊗ id) ∘ α ∣ Γ ]f
  ≐⟨ refl ∘ [≐∣ Γ ] (~ nα) ⟩ 
    ψ _ (_ ⊗ D) Γ ∘ [ α ∘ f ⊗ id ⊗ id ∣ Γ ]f
  ≐⟨ refl ∘ [∘∣ Γ ] _ _ ∙ ~ ass ⟩ 
    ψ _ (_ ⊗ D) Γ ∘ [ α ∣ Γ ]f ∘ [ f ⊗ id ⊗ id ∣ Γ ]f
  qed≐

nφ' : (Γ Δ : Cxt) → {A B : Fma} → (f : A ⇒ B) → 
           [ f ∣ Γ ]f ⊗ id ∘ φ' A Γ Δ ≐ φ' B Γ Δ ∘ [ f ∣ Γ ++ Δ ]f  
nφ' Γ Δ f =
  proof≐
    [ f ∣ Γ ]f ⊗ id ∘ (ψ [ _ ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) 
  ≐⟨ ~ ass ⟩
    [ f ∣ Γ ]f ⊗ id ∘ ψ [ _ ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f
  ≐⟨ nψ Δ [ f ∣ Γ ]f ∘ refl ⟩
    ψ _ I Δ ∘ [ [ f ∣ Γ ]f ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f
  ≐⟨ ass ⟩
    ψ _ I Δ ∘ ([ [ f ∣ Γ ]f ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩
    ψ _ I Δ ∘ [ [ f ∣ Γ ]f ⊗ id ∘ ρ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ nρ) ⟩
    ψ _ I Δ ∘ [ ρ ∘ [ f ∣ Γ ]f ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩
    ψ _ I Δ ∘ ([ ρ ∣ Δ ]f ∘ [ f ∣ Γ ++ Δ ]f)
  ≐⟨ ~ ass ⟩
    ψ _ I Δ ∘ [ ρ ∣ Δ ]f ∘ [ f ∣ Γ ++ Δ ]f
  qed≐

nψ2 : {A B C : Fma} → (Γ : Cxt) → (f : B ⇒ C) → 
       id ⊗ [ f ∣ Γ ]f ∘ ψ A B Γ ≐ ψ A C Γ ∘ [ id ⊗ f ∣ Γ ]f
nψ2 [] f = ~ rid ∙ ~ lid
nψ2 (D ∷ Γ) f =
  proof≐
    id ⊗ [ f ⊗ id ∣ Γ ]f ∘ (ψ _ (_ ⊗ D) Γ ∘ [ α ∣ Γ ]f)
  ≐⟨ ~ ass ⟩ 
    id ⊗ [ f ⊗ id ∣ Γ ]f ∘ ψ _ (_ ⊗ D) Γ ∘ [ α ∣ Γ ]f
  ≐⟨ nψ2 Γ (f ⊗ id) ∘ refl ⟩ 
    ψ _ (_ ⊗ D) Γ ∘ [ id ⊗ (f ⊗ id) ∣ Γ ]f ∘ [ α ∣ Γ ]f
  ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Γ ] _ _) ⟩ 
    ψ _ (_ ⊗ D) Γ ∘ [ id ⊗ (f ⊗ id) ∘ α ∣ Γ ]f
  ≐⟨ refl ∘ [≐∣ Γ ] (~ nα) ⟩ 
    ψ _ (_ ⊗ D) Γ ∘ [ α ∘ id ⊗ f ⊗ id ∣ Γ ]f
  ≐⟨ refl ∘ [∘∣ Γ ] _ _ ∙ ~ ass ⟩ 
    ψ _ (_ ⊗ D) Γ ∘ [ α ∣ Γ ]f ∘ [ id ⊗ f ⊗ id ∣ Γ ]f
  qed≐

nψ2' : {A B C D : Fma} → (Γ Δ : Cxt) → (f : C ⇒ D) → 
       id ⊗ [ id ⊗ f ∣ Δ ]f ∘ ψ A B (Γ ++ C ∷ Δ)
          ≐ ψ A B (Γ ++ D ∷ Δ) ∘ [ id ⊗ f ∣ Δ ]f
nψ2' [] Δ f =
  proof≐
    id ⊗ [ id ⊗ f ∣ Δ ]f ∘ (ψ _ _ Δ ∘ [ α ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    id ⊗ [ id ⊗ f ∣ Δ ]f ∘ ψ _ _ Δ ∘ [ α ∣ Δ ]f
  ≐⟨ nψ2 Δ (id ⊗ f) ∘ refl ⟩ 
    ψ _ _ Δ ∘ [ id ⊗ (id ⊗ f) ∣ Δ ]f ∘ [ α ∣ Δ ]f
  ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _) ⟩ 
    ψ _ _ Δ ∘ [ id ⊗ (id ⊗ f) ∘ α ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ nα) ⟩ 
    ψ _ _ Δ ∘ [ α ∘  id ⊗ id ⊗ f ∣ Δ ]f
  ≐⟨ refl ∘ ([∘∣ Δ ] _ _ ∙ (refl ∘ [≐∣ Δ ] (f⊗id ⊗ refl))) ∙ ~ ass ⟩ 
    ψ _ _ Δ ∘ [ α ∣ Δ ]f ∘ [ id ⊗ f ∣ Δ ]f
  qed≐ 
nψ2' (E ∷ Γ) Δ f =
  proof≐
    id ⊗ [ id ⊗ f ∣ Δ ]f ∘ (ψ _ _ (Γ ++ _ ∷ Δ) ∘ [ [ α ∣ Γ ]f ⊗ id ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    id ⊗ [ id ⊗ f ∣ Δ ]f ∘ ψ _ _ (Γ ++ _ ∷ Δ) ∘ [ [ α ∣ Γ ]f ⊗ id ∣ Δ ]f
  ≐⟨ nψ2' Γ Δ f ∘ refl ⟩ 
    ψ _ _ (Γ ++ _ ∷ Δ) ∘ [ id ⊗ f ∣ Δ ]f ∘ [ [ α ∣ Γ ]f ⊗ id ∣ Δ ]f
  ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _) ⟩ 
    ψ _ _ (Γ ++ _ ∷ Δ) ∘ [ id ⊗ f ∘ [ α ∣ Γ ]f ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] id⊗swap ⟩ 
    ψ _ _ (Γ ++ _ ∷ Δ) ∘ [ [ α ∣ Γ ]f ⊗ id ∘ id ⊗ f ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ∙ ~ ass ⟩ 
    ψ _ _ (Γ ++ _ ∷ Δ) ∘ [ [ α ∣ Γ ]f ⊗ id ∣ Δ ]f ∘ [ id ⊗ f ∣ Δ ]f
  qed≐

nφ'2 : (Γ Δ Λ : Cxt) → {A B C : Fma} → (f : B ⇒ C) → 
           id ⊗ [ id ⊗ f ∣ Λ ]f ∘ φ' A Γ (Δ ++ B ∷ Λ)
             ≐ φ' A Γ (Δ ++ C ∷ Λ) ∘ [ id ⊗ f ∣ Λ ]f
nφ'2 Γ Δ Λ {A} {B} {C} f =
  proof≐
    id ⊗ [ id ⊗ f ∣ Λ ]f ∘ (ψ [ A ∣ Γ ] I (Δ ++ B ∷ Λ) ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Λ ]f)
  ≐⟨ ~ ass ⟩ 
    id ⊗ [ id ⊗ f ∣ Λ ]f ∘ ψ [ A ∣ Γ ] I (Δ ++ B ∷ Λ) ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Λ ]f
  ≐⟨ nψ2' Δ Λ f ∘ refl ⟩ 
    ψ [ A ∣ Γ ] I (Δ ++ C ∷ Λ) ∘ [ id ⊗ f ∣ Λ ]f ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Λ ]f
  ≐⟨ ass ⟩ 
    ψ [ A ∣ Γ ] I (Δ ++ C ∷ Λ) ∘ ([ id ⊗ f ∣ Λ ]f ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Λ ]f)
  ≐⟨ refl ∘ (~ [∘∣ Λ ] _ _ ∙ ([≐∣ Λ ] id⊗swap ∙ [∘∣ Λ ] _ _)) ⟩ 
    ψ [ A ∣ Γ ] I (Δ ++ C ∷ Λ) ∘ ([ [ ρ ∣ Δ ]f ⊗ id ∣ Λ ]f ∘ [ id ⊗ f ∣ Λ ]f)
  ≐⟨ ~ ass ⟩ 
    ψ [ A ∣ Γ ] I (Δ ++ C ∷ Λ) ∘ [ [ ρ ∣ Δ ]f ⊗ id ∣ Λ ]f ∘ [ id ⊗ f ∣ Λ ]f
  qed≐

lψ : {A : Fma} (Γ : Cxt) → l ∘ ψ I A Γ ≐ [ l ∣ Γ ]f
lψ [] = ~ rid
lψ (B ∷ Γ) =
  proof≐
    l ∘ (ψ I (_ ⊗ B) Γ ∘ [ α ∣ Γ ]f)
  ≐⟨ ~ ass ⟩
    l ∘ ψ I (_ ⊗ B) Γ ∘ [ α ∣ Γ ]f
  ≐⟨ lψ Γ ∘ refl ⟩
    [ l ∣ Γ ]f ∘ [ α ∣ Γ ]f
  ≐⟨ ~ [∘∣ Γ ] _ _ ⟩
    [ l ∘ α ∣ Γ ]f
  ≐⟨ [≐∣ Γ ] lα ⟩
    [ l ⊗ id ∣ Γ ]f
  qed≐

lφ' : (Γ : Cxt) → l ∘ φ' I [] Γ ≐ id
lφ' Γ =
  proof≐
    l ∘ (ψ I I Γ ∘ [ ρ ∣ Γ ]f)
  ≐⟨ ~ ass ⟩
    l ∘ ψ I I Γ ∘ [ ρ ∣ Γ ]f
  ≐⟨ lψ Γ ∘ refl ⟩
    [ l ∣ Γ ]f ∘ [ ρ ∣ Γ ]f
  ≐⟨ ~ [∘∣ Γ ] _ _ ⟩
    [ l ∘ ρ ∣ Γ ]f
  ≐⟨ [≐∣ Γ ] lρ ⟩
    [ id ∣ Γ ]f
  ≐⟨ [id∣ Γ ] ⟩
    id
  qed≐



ψ++ : (A B : Fma) → (Δ Λ : Cxt) →
      ψ A B (Δ ++ Λ) ≐ ψ A [ B ∣ Δ ] Λ ∘ [ ψ A B Δ ∣ Λ ]f
ψ++ A B [] Λ = rid ∙ (refl ∘ ~ [id∣ Λ ])
ψ++ A B (C ∷ Δ) Λ =
  ψ++ A (B ⊗ C) Δ Λ ∘ refl
  ∙ ass
  ∙ (refl ∘ ~ [∘∣ Λ ] _ _)


αψ : {A B C : Fma} → (Δ : Cxt) →
      id ⊗ ψ B C Δ ∘ ψ A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f
        ≐ α ∘ ψ (A ⊗ B) C Δ
αψ [] = ~ rid ∘ refl ∙ (f⊗id ∘ refl ∙ lid) ∙ rid
αψ {A}{B}{C} (D ∷ Δ) =
  proof≐
    id ⊗ (ψ B (C ⊗ D) Δ ∘ [ α ∣ Δ ]f) ∘ (ψ A (B ⊗ C ⊗ D) Δ ∘ [ α ∣ Δ ]f) ∘ [ α ⊗ id ∣ Δ ]f
  ≐⟨ ~ ass ∙ (rid ⊗ refl ∙ f⊗∘ ∘ refl ∙ ass ∘ refl) ∘ refl ∙ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _) ⟩
    id ⊗ ψ B (C ⊗ D) Δ ∘ (id ⊗ [ α ∣ Δ ]f ∘ ψ A (B ⊗ C ⊗ D) Δ) ∘ [ α ∘ α ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ nψ2 Δ α ∘ refl ⟩
    id ⊗ ψ B (C ⊗ D) Δ ∘ (ψ A (B ⊗ (C ⊗ D)) Δ ∘ [ id ⊗ α ∣ Δ ]f) ∘ [ α ∘ α ⊗ id ∣ Δ ]f
  ≐⟨ ass ∙ (refl ∘ ass) ∙ (refl ∘ (refl ∘ ~ [∘∣ Δ ] _ _)) ∙ ~ ass ⟩
    id ⊗ ψ B (C ⊗ D) Δ ∘ ψ A (B ⊗ (C ⊗ D)) Δ ∘ [ id ⊗ α ∘ (α ∘ α ⊗ id) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ααα) ⟩
    id ⊗ ψ B (C ⊗ D) Δ ∘ ψ A (B ⊗ (C ⊗ D)) Δ ∘ [ α ∘ α ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ∙ ~ ass ⟩
    id ⊗ ψ B (C ⊗ D) Δ ∘ ψ A (B ⊗ (C ⊗ D)) Δ ∘ [ α ∣ Δ ]f ∘ [ α ∣ Δ ]f
  ≐⟨ αψ Δ ∘ refl ⟩
    α ∘ ψ (A ⊗ B) (C ⊗ D) Δ ∘ [ α ∣ Δ ]f
  ≐⟨ ass ⟩
    α ∘ (ψ (A ⊗ B) (C ⊗ D) Δ ∘ [ α ∣ Δ ]f)
  qed≐

αφ' : {A : Fma} → (Γ Δ Λ : Cxt) →
      id ⊗ φ' I Δ Λ ∘ φ' A Γ (Δ ++ Λ) ≐ α ∘ φ' A Γ Δ ⊗ id ∘ φ' [ A ∣ Γ ] Δ Λ
αφ' {A} Γ Δ Λ =
  proof≐
    id ⊗ φ' I Δ Λ ∘ φ' A Γ (Δ ++ Λ)
  ≐⟨ refl ∘ (ψ++  _ _ Δ Λ ∘ refl) ⟩
    id ⊗ (ψ [ I ∣ Δ ] I Λ ∘ [ ρ ∣ Λ ]f) ∘ (ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∘ [ ψ [ A ∣ Γ ] I Δ ∣ Λ ]f ∘ [ [ ρ ∣ Δ ]f ∣ Λ ]f)
  ≐⟨ rid ⊗ refl  ∘ refl ∙ (f⊗∘ ∘ refl) ⟩
    id ⊗ ψ [ I ∣ Δ ] I Λ ∘ id ⊗ [ ρ ∣ Λ ]f ∘ (ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∘ [ ψ [ A ∣ Γ ] I Δ ∣ Λ ]f ∘ [ [ ρ ∣ Δ ]f ∣ Λ ]f)
  ≐⟨ ~ ass ∙ (~ ass ∙ (ass ∘ refl) ∘ refl) ⟩
    id ⊗ ψ [ I ∣ Δ ] I Λ ∘ (id ⊗ [ ρ ∣ Λ ]f ∘ ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ) ∘ [ ψ [ A ∣ Γ ] I Δ ∣ Λ ]f ∘ [ [ ρ ∣ Δ ]f ∣ Λ ]f
  ≐⟨ refl ∘ nψ2 Λ ρ ∘ refl ∘ refl ⟩
    id ⊗ ψ [ I ∣ Δ ] I Λ ∘ (ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ I) Λ ∘ [ id ⊗ ρ ∣ Λ ]f) ∘ [ ψ [ A ∣ Γ ] I Δ ∣ Λ ]f ∘ [ [ ρ ∣ Δ ]f ∣ Λ ]f
  ≐⟨ ass ∙ (ass ∙ (refl ∘ (ass ∙ (refl ∘ (refl ∘ ~ [∘∣ Λ ] _ _ ∙ (~ [∘∣ Λ ] _ _ )))))) ∙ ~ ass ⟩
    id ⊗ ψ [ I ∣ Δ ] I Λ ∘ ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ I) Λ ∘ [ id ⊗ ρ ∘ (ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] (~ αρ ∘ refl) ⟩
    id ⊗ ψ [ I ∣ Δ ] I Λ ∘ ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ I) Λ ∘ [ α ∘ ρ ∘ (ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ∣ Λ ]f
  ≐⟨ refl ∘ [≐∣ Λ ] (ass ∙ (refl ∘ nρ) ∙ ~ ass) ⟩
    id ⊗ ψ [ I ∣ Δ ] I Λ ∘ ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ I) Λ ∘ [ α ∘ (ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ⊗ id ∘ ρ ∣ Λ ]f
  ≐⟨ refl ∘ ([∘∣ Λ ] _ _ ∙ ([∘∣ Λ ] _ _ ∘ refl)) ∙ (~ ass ∙ (~ ass ∘ refl)) ⟩
    id ⊗ ψ [ I ∣ Δ ] I Λ ∘ ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ I) Λ ∘ [ α ∣ Λ ]f ∘ [ (ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ⊗ id ∣ Λ ]f ∘ [ ρ ∣ Λ ]f
  ≐⟨ αψ Λ ∘ refl ∘ refl ⟩
    α ∘ ψ ([ A ∣ Γ ] ⊗ [ I ∣ Δ ]) I Λ ∘ [ (ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ⊗ id ∣ Λ ]f ∘ [ ρ ∣ Λ ]f
  ≐⟨ ass ∘ refl ⟩
    α ∘ (ψ ([ A ∣ Γ ] ⊗ [ I ∣ Δ ]) I Λ ∘ [ (ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ⊗ id ∣ Λ ]f) ∘ [ ρ ∣ Λ ]f
  ≐⟨ refl ∘ ~ nψ Λ _ ∘ refl ⟩
    α ∘ ((ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ⊗ id ∘ ψ [ [ A ∣ Γ ] ∣ Δ ] I Λ) ∘ [ ρ ∣ Λ ]f
  ≐⟨ ~ ass ∘ refl ∙ ass ⟩
    α ∘ (ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f) ⊗ id ∘ (ψ [ [ A ∣ Γ ] ∣ Δ ] I Λ ∘ [ ρ ∣ Λ ]f)
  qed≐

φ'++ : (A : Fma) → (Γ Δ Λ : Cxt) →
      φ' A Γ (Δ ++ Λ) ≐ ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∘ [ φ' A Γ Δ ∣ Λ ]f
φ'++ A Γ Δ Λ =
  proof≐
    ψ [ A ∣ Γ ] I (Δ ++ Λ) ∘ [ [ ρ ∣ Δ ]f ∣ Λ ]f
  ≐⟨ ψ++ _ _ Δ Λ ∘ refl ⟩ 
    ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∘ [ ψ [ A ∣ Γ ] I Δ ∣ Λ ]f ∘ [ [ ρ ∣ Δ ]f ∣ Λ ]f
  ≐⟨ ass ⟩ 
    ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∘ ([ ψ [ A ∣ Γ ] I Δ ∣ Λ ]f ∘ [ [ ρ ∣ Δ ]f ∣ Λ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Λ ] _ _ ⟩ 
    ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∘ [ ψ [ A ∣ Γ ] I Δ ∘ [ ρ ∣ Δ ]f ∣ Λ ]f
  qed≐

assφ' : {A : Fma} → (Γ Δ Λ Π : Cxt) →
      id ⊗ [ φ' I Δ Λ ∣ Π ]f ∘ φ' A Γ (Δ ++ Λ ++ Π)
        ≐ φ' A Γ (Δ ++ [ I ∣ Λ ] ∷ Π) ∘ [ φ' A (Γ ++ Δ) Λ ∣ Π ]f
        -- 
assφ' {A} Γ Δ Λ Π =
  proof≐
    id ⊗ [ φ' I Δ Λ ∣ Π ]f ∘ φ' A Γ (Δ ++ Λ ++ Π)
  ≐⟨ refl ∘ φ'++ A Γ (Δ ++ Λ) Π ∙ (refl ∘ (refl ∘ [≐∣ Π ] (φ'++ A Γ Δ Λ))) ⟩
    id ⊗ [ φ' I Δ Λ ∣ Π ]f ∘ (ψ [ A ∣ Γ ] [ [ I ∣ Δ ] ∣ Λ ] Π ∘ [ ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∘ [ φ' A Γ Δ ∣ Λ ]f ∣ Π ]f)
  ≐⟨ refl ∘ (refl ∘ [∘∣ Π ] _ _) ∙ (refl ∘ ~ ass) ⟩ 
    id ⊗ [ φ' I Δ Λ ∣ Π ]f ∘ (ψ [ A ∣ Γ ] [ [ I ∣ Δ ] ∣ Λ ] Π ∘ [ ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∣ Π ]f ∘ [ [ φ' A Γ Δ ∣ Λ ]f ∣ Π ]f)
  ≐⟨ ~ ass ∙ (~ ass ∘ refl) ⟩ 
    id ⊗ [ φ' I Δ Λ ∣ Π ]f ∘ ψ [ A ∣ Γ ] [ I ∣ Δ ++ Λ ] Π ∘ [ ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∣ Π ]f ∘ [ [ φ' A Γ Δ ∣ Λ ]f ∣ Π ]f 
  ≐⟨ nψ2 Π _ ∘ refl ∘ refl ⟩ 
    ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ [ I ∣ Λ ]) Π ∘ [ id ⊗ φ' I Δ Λ ∣ Π ]f ∘ [ ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∣ Π ]f ∘ [ [ φ' A Γ Δ ∣ Λ ]f ∣ Π ]f 
  ≐⟨ ass ∙ (ass ∙ (refl ∘ (refl ∘ ~ [∘∣ Π ] _ _ ∙ ~ [∘∣ Π ] _ _))) ⟩ 
    ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ [ I ∣ Λ ]) Π ∘ [ id ⊗ φ' I Δ Λ ∘ (ψ [ A ∣ Γ ] [ I ∣ Δ ] Λ ∘ [ φ' A Γ Δ ∣ Λ ]f) ∣ Π ]f
  ≐⟨ refl ∘ [≐∣ Π ] (refl ∘ ~ φ'++ A Γ Δ Λ) ⟩ 
    ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ [ I ∣ Λ ]) Π ∘ [ id ⊗ φ' I Δ Λ ∘ φ' A Γ (Δ ++ Λ) ∣ Π ]f
  ≐⟨ refl ∘ [≐∣ Π ] (αφ' Γ Δ Λ) ⟩ 
    ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ [ I ∣ Λ ]) Π ∘ [ α ∘ φ' A Γ Δ ⊗ id ∘ φ' A (Γ ++ Δ) Λ ∣ Π ]f
  ≐⟨ refl ∘ ([≐∣ Π ] ass ∙ [∘∣ Π ] _ _ ∙ (refl ∘ [∘∣ Π ] _ _)) ∙ ~ ass ∙ ~ ass ⟩ 
    ψ [ A ∣ Γ ] ([ I ∣ Δ ] ⊗ [ I ∣ Λ ]) Π ∘ [ α ∣ Π ]f ∘ [ φ' A Γ Δ ⊗ id ∣ Π ]f ∘ [ φ' A (Γ ++ Δ) Λ ∣ Π ]f
  ≐⟨ ~ φ'++ A Γ Δ ([ I ∣ Λ ] ∷ Π)  ∘ refl ⟩ 
    φ' A Γ (Δ ++ [ I ∣ Λ ] ∷ Π) ∘ [ φ' A (Γ ++ Δ) Λ ∣ Π ]f
  qed≐ 

