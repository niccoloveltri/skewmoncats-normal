
{- =========================================================== -}
-- Proof theory of left-normal skew-monoidal categories
{- =========================================================== -}


module Everything where


-- Utilities file
open import Utilities

-- The free left-normal skew monoidal category on a set of generators,
-- a.k.a the categorical calculus.
open import Fsk

-- Three equivalent sequent calculi:
-- (i)   cut-free sequent calculus,
-- (ii)  focused calculus with stoup
-- (iii) focused calculus without stoup
open import SeqCalc

-- Some properties of the cut rules in the focused sequent calculus.
open import MulticatLaws

-- Soundness, i.e. interpretation of focused calculus derivations as
-- categorical calculus derivations.
open import Sound

-- Completeness, i.e. interpretation of categorical derivations as
-- focused calculus derivations. 
open import Complete
open import StrongComplete
open import EqComplete

-- Proof that the soundness map is an isomorphism, with the
-- completeness map as its inverse.
open import SoundComplete
open import CompleteSound

