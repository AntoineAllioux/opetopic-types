{-# OPTIONS --without-K --rewriting --allow-unsolved-meta #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import Algebricity
open import Algebras

module AlgebrasOver where

  module SourceHelper↓ {M : 𝕄} (M↓ : 𝕄↓ M)
                       {X : Idx (Slice M) → Set}
                       (X↓ : (i : Idx (Slice  M)) → Idx↓ (Slice↓ M↓) i → X i → Set)
                       {i : Idx M} (i↓ : Idx↓ M↓ i)
                       {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
                       {δ : (p : Pos M c) → Cns M (Typ M c p)}
                       (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
                       {x : X (i , c)} (x↓ : X↓ (i , c) (i↓ , c↓) x)
                       {xδ : (p : Pos M c) → X (Typ M c p , δ p)}
                       (xδ↓ : (p : Pos M c) → X↓ _ (Typ↓ M↓ c↓ p , δ↓ p) (xδ p)) where
                         
    open SourceHelper M X i c δ x xδ public

    μX-tr↓ : Pd↓ M↓ (i↓ , μ↓ M↓ c↓ δ↓) μX-tr
    μX-tr↓ = nd↓ c↓ δ↓ (λ p → η↓ (Slice↓ M↓) (Typ↓ M↓ c↓ p , δ↓ p)) 

    θX↓ : (p : Pos (Slice M) μX-tr) → X↓ _ (Typ↓ (Slice↓ M↓) μX-tr↓ p) (θX p)
    θX↓ true = x↓
    θX↓ (inr (p , true)) = xδ↓ p


  module _ {M : 𝕄} (M↓ : 𝕄↓ M) where
    open import SliceUnfoldOver M↓
    
    module CompHelper↓ {X₀ : Rel₀} (X₀↓ : Rel₀↓ X₀)
             {X₁ : Rel₁ X₀} (X₁↓ : Rel₁↓ X₀↓ X₁)
             (is-fib-X₁↓ : is-fib₁↓ X₀↓ X₁↓) where
             
      open CompHelper M

      comp↓ : {i : Idx M} {i↓ : Idx↓ M↓ i}
        → {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
        → {ν : (p : Pos M c) → X₀ (Typ M c p)}
        → (ν↓ : (p : Pos M c) → X₀↓ (Typ M c p) (Typ↓ M↓ c↓ p) (ν p))
        → (x₀ : X₀ i) (x₁ : X₁ ((i , x₀) , c , ν))
        → X₀↓ i i↓ x₀
      comp↓ {c = c} c↓ {ν = ν} ν↓ x₀ x₁ = fst $ contr-center $ is-fib-X₁↓ _ c↓ ν↓ x₀ x₁

      fill↓ : {i : Idx M} {i↓ : Idx↓ M↓ i}
        → {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
        → {ν : (p : Pos M c) → X₀ (Typ M c p)}
        → (ν↓ : (p : Pos M c) → X₀↓ (Typ M c p) (Typ↓ M↓ c↓ p) (ν p))
        → (x₀ : X₀ i) (x₁ : X₁ ((i , x₀) , c , ν))
        → X₁↓ ((i , x₀) , c , ν)
              ((i↓ , comp↓ c↓ ν↓ x₀ x₁) , c↓ , ν↓)
              x₁
      fill↓ {c = c} c↓ {ν = ν} ν↓ x₀ x₁ = snd $ contr-center $ is-fib-X₁↓ _ c↓ ν↓ x₀ x₁

  module _ {M : 𝕄} (M↓ : 𝕄↓ M) where

    open import SliceUnfoldOver M↓
    open ExtUnfold M↓
    
    module AlgStruct↓ {X₀ : Rel₀} (X₀↓ : Rel₀↓ X₀)
                      {X₁ : Rel₁ X₀} (X₁↓ : Rel₁↓ X₀↓ X₁)
                      {X₂ : Rel₂ X₁} (X₂↓ : Rel₂↓ X₀↓ X₁↓ X₂)
                      (is-fib-X₂ : is-fib₂ X₂) (is-fib-X₂↓ : is-fib₂↓ X₀↓ X₁↓ X₂↓) where

      open AlgStruct M X₀ X₁ X₂ is-fib-X₂
      open CompHelper↓ (Slc₁↓ X₀↓) X₁↓ X₂↓ is-fib-X₂↓

      ηX↓ : {i : Idx M} (i↓ : Idx↓ M↓ i)
        → {x₀ : X₀ i} (x₀↓ : X₀↓ i i↓ x₀)
        → X₁↓ ((i , x₀) , η M i , η-dec M X₀ x₀)
              ((i↓ , x₀↓) , η↓ M↓ i↓ , η↓-dec M↓ X₀↓ x₀↓)
              (ηX i x₀)
      ηX↓ {i} i↓ {x₀} x₀↓ = comp↓ (lf↓ (i↓ , x₀↓)) ⊥-elim (ηX i x₀) (ηX-fill i x₀)
      
      ηX-fill↓ : {i : Idx M} (i↓ : Idx↓ M↓ i)
        → {x₀ : X₀ i} (x₀↓ : X₀↓ i i↓ x₀)
        → X₂↓ ((((i , x₀) , η M i , η-dec M X₀ x₀) , ηX i x₀) , lf (i , x₀) , ⊥-elim)
              ((_ , ηX↓ i↓ x₀↓) , lf↓ (i↓ , x₀↓) , ⊥-elim)
              (ηX-fill i x₀) 
      ηX-fill↓ {i} i↓ {x₀} x₀↓ = fill↓ (lf↓ (i↓ , x₀↓)) ⊥-elim (ηX i x₀) (ηX-fill i x₀)

      module _ {i : Idx M} (i↓ : Idx↓ M↓ i)
               {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
               {ν : (p : Pos M c) → X₀ (Typ M c p)}
               (ν↓ : (p : Pos M c) → X₀↓ (Typ M c p) (Typ↓ M↓ c↓ p) (ν p))
               {δ : (p : Pos M c) → Cns (Pb M X₀) (Typ M c p , ν p)}
               (δ↓ : (p : Pos M c) → Cns↓ (Pb↓ M↓ X₀ X₀↓) (Typ↓ M↓ c↓ p , ν↓ p) (δ p))
               {x₀ : X₀ i} (x₀↓ : X₀↓ i i↓ x₀)
               {x₁ : X₁ ((i , x₀) , c , ν)} (x₁↓ : X₁↓ ((i , x₀) , c , ν) ((i↓ , x₀↓) , c↓ , ν↓) x₁)
               {ε : (p : Pos M c) → X₁ ((Typ M c p , ν p) , (δ p))}
               (ε↓ : (p : Pos M c) → X₁↓ ((Typ M c p , ν p) , (δ p)) ((Typ↓ M↓ c↓ p , ν↓ p) , (δ↓ p)) (ε p)) where
               
        open SourceHelper↓ (Pb↓ M↓ X₀ X₀↓) X₁↓ (i↓ , x₀↓) (c↓ , ν↓) δ↓ x₁↓ ε↓

        μX↓ : X₁↓ _ ((i↓ , x₀↓) , μ↓ (Pb↓ M↓ X₀ X₀↓) {i↓ = i↓ , x₀↓} (c↓ , ν↓) δ↓) (μX _ _ _ _ _ x₁ ε)
        μX↓ = comp↓ μX-tr↓ θX↓ (μX _ _ _ _ _ x₁ ε) (μX-fill _ _ _ _ _ x₁ ε) 

        μX-fill↓ : X₂↓ _ ((((i↓ , x₀↓) , μ↓ (Pb↓ M↓ X₀ X₀↓) {i↓ = i↓ , x₀↓} (c↓ , ν↓) δ↓) , μX↓) , μX-tr↓ , θX↓) (μX-fill _ _ _ _ _ x₁ ε)
        μX-fill↓ = fill↓ μX-tr↓ θX↓ (μX _ _ _ _ _ x₁ ε) (μX-fill _ _ _ _ _ x₁ ε) 

      module Laws {X₂ : Rel₂ X₁} (X₂↓ : Rel₂↓ X₀↓ X₁↓ X₂)
                  (is-fib-X₂ : is-fib₂ X₂)
                  (is-fib-X₂↓ : is-fib₂↓ X₀↓ X₁↓ X₂↓) where
