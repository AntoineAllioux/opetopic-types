{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
import SliceUnfold

module SliceUnfoldOver {M : 𝕄} (M↓ : 𝕄↓ M) where

  open SliceUnfold M public

  Rel₀↓ : Rel₀ → Set₁
  Rel₀↓ X₀ = (i : Idx M) → Idx↓ M↓ i → X₀ i → Set

  module _ {X₀ : Rel₀} (X₀↓ : Rel₀↓ X₀) where

    Plbk₁↓ : 𝕄↓ (Plbk₁ X₀)
    Plbk₁↓ = Pb↓ M↓ X₀ X₀↓

    Slc₁↓ : 𝕄↓ (Slc₁ X₀)
    Slc₁↓ = Slice↓ Plbk₁↓

    Rel₁↓ : Rel₁ X₀ → Set₁ 
    Rel₁↓ X₁ = (i : Idx (Slc₁ X₀)) → Idx↓ Slc₁↓ i → X₁ i → Set

  module _ {X₀ : Rel₀} (X₀↓ : Rel₀↓ X₀)
           {X₁ : Rel₁ X₀} (X₁↓ : Rel₁↓ X₀↓ X₁) where

    is-fib₁↓ : Set
    is-fib₁↓ = unique-action↓ M↓ X₀↓ X₁↓

    Plbk₂↓ : 𝕄↓ (Plbk₂ X₁)
    Plbk₂↓ = Pb↓ (Slc₁↓ X₀↓) X₁ X₁↓

    Slc₂↓ : 𝕄↓ (Slc₂ X₁)
    Slc₂↓ = Slice↓ Plbk₂↓

    Rel₂↓ : Rel₂ X₁ → Set₁
    Rel₂↓ X₂ = (i : Idx (Slc₂ X₁)) → Idx↓ Slc₂↓ i → X₂ i → Set 


  module _ {X₀ : Rel₀} (X₀↓ : Rel₀↓ X₀)
           {X₁ : Rel₁ X₀} (X₁↓ : Rel₁↓ X₀↓ X₁)
           {X₂ : Rel₂ X₁} (X₂↓ : Rel₂↓ X₀↓ X₁↓ X₂) where

    is-fib₂↓ : Set
    is-fib₂↓ = unique-action↓ (Slice↓ (Pb↓ M↓ X₀ X₀↓)) X₁↓ X₂↓
