
{- =========================================================== -}
-- Proof theory of associative-normal skew-monoidal categories
{- =========================================================== -}

module Everything where

-- Utilities file
open import Utilities

-- The free associative-normal skew monoidal category on a set of
-- generators, a.k.a the categorical calculus.
open import Fsk

-- A cut-free sequent calculus.
open import SeqCalc

-- Admissible cut rules, plus some lemmata related to cuts.
open import Cuts
-- Some more properties of the cut rules in the focused sequent
-- calculus.
open import MulticatLaws1
open import MulticatLaws2

-- Soundness, i.e. interpretation of sequent calculus derivations as
-- categorical calculus derivations.
open import Sound
open import EqSound

-- Completeness, i.e. interpretation of categorical derivations as
-- sequent calculus derivations. 
open import Complete
open import EqComplete
open import StrongComplete

-- Proof that the soundness map is an isomorphism, with the
-- completeness map as its inverse.
open import SoundComplete
open import CompleteSound

-- A focused sequent calculus, equivalent to the unfocused sequent
-- calculus
open import Focusing
