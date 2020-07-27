{-# OPTIONS --without-K --rewriting --allow-unsolved-meta #-}

open import Monad
open import MonadOver
open import OpetopicType
open import Pb
open import SigmaMonad
open import HoTT

module Sigma where
 
  Ob-Σ : (M : 𝕄) (M↓ : 𝕄↓ M)
    → (A : Idx M → Set) (A↓ : (i : Idx M) → Idx↓ M↓ i → A i → Set)
    → Σ (Idx M) (Idx↓ M↓)
    → Set
  Ob-Σ M M↓ A A↓ (i , j) = Σ (A i) (A↓ i j)

  postulate

    PbΣM : (M : 𝕄) (M↓ : 𝕄↓ M) (X : OpetopicType M) (X↓ : OpetopicTypeOver M↓ X)
      → (A : Idx M → Set) (A↓ : (i : Idx M) → Idx↓ M↓ i → A i → Set)
      → ΣM (Pb M A) (Pb↓ M↓ A A↓)
        ↦ Pb (ΣM M M↓) (Ob-Σ M M↓ A A↓)
    {-# REWRITE PbΣM  #-}

    SliceΣM : (M : 𝕄) (M↓ : 𝕄↓ M) (X : OpetopicType M) (X↓ : OpetopicTypeOver M↓ X)
      → ΣM (Slice M) (Slice↓ M↓)
        ↦ Slice (ΣM M M↓)
    {-# REWRITE SliceΣM  #-}

  Σ𝕆 : (M : 𝕄) (M↓ : 𝕄↓ M) (X : OpetopicType M)
    → (X↓ : OpetopicTypeOver M↓ X)
    → OpetopicType (ΣM M M↓)
  Ob (Σ𝕆 M M↓ X X↓) = Ob-Σ M M↓ (Ob X) (Ob↓ X↓) 
  Hom (Σ𝕆 M M↓ X X↓) = {!!} -- Σ𝕆 (Slice (Pb M (Ob X))) (Slice↓ (Pb↓ M↓ (Ob X) (Ob↓ X↓))) (Hom X) (Hom↓ X↓)
