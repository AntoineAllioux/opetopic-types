{-# OPTIONS --without-K --rewriting --allow-unsolved-meta #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import Algebricity

module AlgEqvElim where

  module Stuff (M : 𝕄) where

    open import SliceUnfold M

    module _ {X₀ : Rel₀} {X₁ : Rel₁ X₀} (is-fib-X₁ : is-fib₁ X₁) where

      comp : {i : Idx M}
        → (c : Cns M i)
        → (ν : (p : Pos M c) → X₀ (Typ M c p))
        → X₀ i
      comp c ν = fst $ contr-center $ is-fib-X₁ _ c ν

      fill : {i : Idx M}
        → (c : Cns M i)
        → (ν : (p : Pos M c) → X₀ (Typ M c p))
        → X₁ ((i , comp c ν) , c , ν)
      fill c ν = snd $ contr-center $ is-fib-X₁ _ c ν

  module _ (M : 𝕄) where

    open import SliceUnfold M

    

    -- The unit and multiplication induced by a fibrant 2-relation
    module AlgStruct (X₀ : Rel₀) (X₁ : Rel₁ X₀)
                     (X₂ : Rel₂ X₁) (is-fib-X₂ : is-fib₂ X₂) where
      open Stuff (Slc₁ X₀)

      -- μX (ηX ...) ??? = μX ----
      -- μX (μX .....) ??? = μx ... (λ → .....)

      ηX : (i : Idx M) (x₀ : X₀ i)
        → X₁ ((i , x₀) , η M i , η-dec M X₀ x₀)
      ηX i x₀ = comp is-fib-X₂ (lf (i , x₀)) ⊥-elim
      
      ηX-fill : (i : Idx M) (x₀ : X₀ i)
        → X₂ ((((i , x₀) , η M i , η-dec M X₀ x₀) , ηX i x₀) , lf (i , x₀) , ⊥-elim)
      ηX-fill i x₀ = fill is-fib-X₂ (lf (i , x₀)) ⊥-elim

      module _ (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → X₀ (Typ M c p))
               (δ : (p : Pos M c) → Cns (Pb M X₀) (Typ M c p , ν p))
               (x₀ : X₀ i) (x₁ : X₁ ((i , x₀) , c , ν))
               (δ↓ : (p : Pos M c) → X₁ ((Typ M c p , ν p) , (δ p))) where

        μX-tr : Pd (Pb M X₀) ((i , x₀) , μ (Pb M X₀) {i = i , x₀} (c , ν) δ)
        μX-tr = nd (c , ν) δ (λ p → η (Slice (Pb M X₀)) ((Typ M c p , ν p) , δ p))

        θX : (p : Pos (Slice (Pb M X₀)) μX-tr) → X₁ (Typ (Slice (Pb M X₀)) μX-tr p)
        θX true = x₁
        θX (inr (p , true)) = δ↓ p

        μX : X₁ ((i , x₀) , μ (Pb M X₀) {i = i , x₀} (c , ν) δ)
        μX = comp is-fib-X₂ μX-tr θX

        μX-fill : X₂ ((((i , x₀) , μ (Pb M X₀) {i = i , x₀} (c , ν) δ) , μX) , μX-tr , θX)
        μX-fill = fill is-fib-X₂ μX-tr θX

      -- Types of the laws satisfied by μX
      module _ (X₃ : Rel₃ X₂) (is-fib-X₃ : is-fib₃ X₃) where

        module _ (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → X₀ (Typ M c p))
                 (x₀ : X₀ i) (x₁ : X₁ ((i , x₀) , c , ν)) where   
        
          μX-unit-r : μX i c ν (λ p → η (Pb M X₀) (Typ (Pb M X₀) {i = i , x₀} (c , ν) p))
                         x₀ x₁ (λ p → ηX (Typ M c p) (ν p))
                      ==  x₁ 
          μX-unit-r = {!!}

        module _ (i : Idx M) (x₀ : X₀ i)
                 (δ : (p : Pos M (η M i)) →  Cns (Pb M X₀) (Typ M (η M i) p , x₀))
                 (δ↓ : (p : Pos M (η M i)) → X₁ ((Typ M (η M i) p , η-dec M X₀ x₀ p) , (δ p))) where

          μX-unit-l : μX i (η M i) (η-dec M X₀ x₀) δ x₀ (ηX i x₀) δ↓ == δ↓ (η-pos M i) 
          μX-unit-l = {!!}

        module _ (i  : Idx M) (c : Cns M i) (ν : (p : Pos M c) → X₀ (Typ M c p))
                 (δ  : (p : Pos M c)
                       → Cns (Pb M X₀) (Typ M c p , ν p)) (x₀ : X₀ i) (x₁ : X₁ ((i , x₀) , c , ν))
                 (δ↓ : (p : Pos M c) → X₁ ((Typ M c p , ν p) , (δ p)))
                 (ε  : (p : Pos M (μ M c (fst ∘ δ)))
                       → Cns (Pb M X₀) (Typ (Pb M X₀) {i = i , x₀} (μ (Pb M X₀) {i = i , x₀} (c , ν) δ) p))
                 (ε↓ : (p : Pos M (μ M c (fst ∘ δ)))
                       → X₁ (Typ (Pb M X₀) {i = i , x₀} (μ (Pb M X₀) {i = i , x₀} (c , ν) δ) p , ε p)) where
                      
          μX-assoc : μX i c ν (λ p → μ (Pb M X₀) {i = Typ M c p , ν p} (δ p) (ε ∘ (μ-pos M c (fst ∘ δ) p)))
                        x₀ x₁
                        (λ p → μX (Typ M c p) (fst (δ p)) (snd (δ p)) (ε ∘ (μ-pos M c (fst ∘ δ) p))
                                  (ν p) (δ↓ p)
                                  λ q → ε↓ (μ-pos M c (fst ∘ δ) p q))
                     == μX i (μ M c (fst ∘ δ))
                           (λ p → snd (δ (μ-pos-fst M c (fst ∘ δ) p)) (μ-pos-snd M c (fst ∘ δ) p))
                           ε
                           x₀ (μX i c ν δ x₀ x₁ δ↓)
                           ε↓
          μX-assoc = {!!}

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    open import SliceUnfold M 
    open ExtUnfold M↓

    module _ (X₁ : Rel₁ (Idx↓ M↓)) (X₂ : Rel₂ X₁) (is-fib-X₂ : is-fib₂ X₂) where

      open AlgStruct _ (Idx↓ M↓) X₁ X₂ is-fib-X₂

      record AlgEqv : Set where
        field 

          e : (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i ≃ X₁ i

          η-hyp : (i : Idx ExtPlbk₁) (j : Idx↓ ExtPlbk↓₁ i)
            → –> (e (i , η ExtPlbk₁ i)) (j , η↓ ExtPlbk↓₁ j)
              == ηX (fst i) (snd i)

          -- Here we should add the hypothesis that there is a non-trivial
          -- decoration.
          μ-hyp : (i : Idx ExtPlbk₁) (c : Cns ExtPlbk₁ i)
            → (δ : (p : Pos ExtPlbk₁ {i = i} c) → Cns ExtPlbk₁ (Typ ExtPlbk₁ {i = i} c p))
            → (j : Idx↓ ExtPlbk↓₁ i) (d : Cns↓ ExtPlbk↓₁ j c)
            → (δ↓ : (p : Pos ExtPlbk₁ {i = i} c) → Cns↓ ExtPlbk↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j} d p) (δ p))
            → –> (e (i , μ ExtPlbk₁ {i = i} c δ)) (j , μ↓ ExtPlbk↓₁ {i↓ = j} d δ↓)
              == μX (fst i) (fst c) (snd c) δ (snd i) (–> (e (i , c)) (j , d))
                    (λ p → –> (e ((Typ M (fst c) p , snd c p) , δ p)) ((Typ↓ M↓ (fst d) p , snd d p) , δ↓ p ))

    module _ (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂) where

      open AlgStruct _ (Idx↓ M↓) (↓Rel₁) X₂ is-fib-X₂

      -- postulate

      --   lf-hyp' : (i : Idx M) (j : Idx↓ M↓ i)
      --     → (j , idp) , η↓ M↓ j , η↓-dec M↓ (λ i j k → j == k) idp == ηX i j

      record AlgFib : Set where
        field

          lf-hyp : (i : Idx ExtPlbk₁) (j : Idx↓ ExtPlbk↓₁ i)
            → (j , η↓ ExtPlbk↓₁ j) == ηX (fst i) (snd i)

          nd-hyp : (i : Idx ExtPlbk₁) (c : Cns ExtPlbk₁ i)
            → (δ : (p : Pos ExtPlbk₁ {i = i} c) → Cns ExtPlbk₁ (Typ ExtPlbk₁ {i = i} c p))
            → (j : Idx↓ ExtPlbk↓₁ i) (d : Cns↓ ExtPlbk↓₁ j c)
            → (δ↓ : (p : Pos ExtPlbk₁ {i = i} c) → Cns↓ ExtPlbk↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j} d p) (δ p))
            → (j , μ↓ ExtPlbk↓₁ {i↓ = j} d δ↓)
              == μX (fst i) (fst c) (snd c) δ (snd i) (j , d)
                    (λ p → (Typ↓ M↓ (fst d) p , snd d p) , δ↓ p)

      open AlgFib
      
      to-alg-eqv : (alg-fib : AlgFib) → AlgEqv ↓Rel₁ X₂ is-fib-X₂
      AlgEqv.e (to-alg-eqv alg-fib) i = ide (↓Rel₁ i)
      AlgEqv.η-hyp (to-alg-eqv alg-fib) = lf-hyp alg-fib
      AlgEqv.μ-hyp (to-alg-eqv alg-fib) = nd-hyp alg-fib

    module AlgElim (P : (X₁ : Rel₁ (Idx↓ M↓)) (X₂ : Rel₂ X₁) (is-fib-X₂ : is-fib₂ X₂) (alg-eqv : AlgEqv X₁ X₂ is-fib-X₂) → Type₀)
                   (id* : (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂) (alg-fib : AlgFib X₂ is-fib-X₂)
                      → P ↓Rel₁ X₂ is-fib-X₂ (to-alg-eqv X₂ is-fib-X₂ alg-fib)) where

      postulate
      
        elim : (X₁ : Rel₁ (Idx↓ M↓)) (X₂ : Rel₂ X₁) (is-fib-X₂ : is-fib₂ X₂) (alg-eqv : AlgEqv X₁ X₂ is-fib-X₂)
          → P X₁ X₂ is-fib-X₂ alg-eqv

