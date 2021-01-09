{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import Algebricity

module AlgEqvElim where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    open import SliceUnfold M 
    open ExtUnfold M↓

    AlgEqv : (X₁ : Rel₁ (Idx↓ M↓)) → Set
    AlgEqv X₁ = (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i ≃ X₁ i

    ΣAlgEqv-is-contr : is-contr (Σ (Rel₁ (Idx↓ M↓)) AlgEqv)
    ΣAlgEqv-is-contr = equiv-preserves-level
      (Σ-emap-r (λ X₁ → Π-emap-r (λ i → ua-equiv ⁻¹) ∘e (λ=-equiv ⁻¹)))
      ⦃ pathfrom-is-contr (Idx↓ ExtSlc↓₁) ⦄

    -- The unit and multiplication induced by a fibrant 2-relation
    module AlgStruct (X₀ : Rel₀) (X₁ : Rel₁ X₀)
                     (X₂ : Rel₂ X₁) (is-fib-X₂ : is-fib₂ X₂) where

      ηX : (i : Idx M) (x₀ : X₀ i)
        → X₁ ((i , x₀) , η M i , cst x₀)
      ηX i x₀ = fst (contr-center (is-fib-X₂ ((i , x₀) , η M i , cst x₀) (lf (i , x₀)) ⊥-elim)) 


      module _ (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → X₀ (Typ M c p))
               (δ : (p : Pos M c) → Cns (Pb M X₀) (Typ M c p , ν p))
               (x₀ : X₀ i) (x₁ : X₁ ((i , x₀) , c , ν))
               (δ↓ : (p : Pos M c) → X₁ ((Typ M c p , ν p) , (δ p))) where

        μX-tr : Pd (Pb M X₀) ((i , x₀) , μ (Pb M X₀) {i = i , x₀} (c , ν) δ)
        μX-tr = nd (c , ν) δ (λ p →
                nd (δ p) (λ q → η (Pb M X₀) (Typ (Pb M X₀) {i = Typ M c p , ν p} (δ p) q)) (λ q →
                lf (Typ (Pb M X₀) {i = Typ M c p , ν p} (δ p) q)))

        θX : (p : Pos (Slice (Pb M X₀)) μX-tr) → X₁ (Typ (Slice (Pb M X₀)) μX-tr p)
        θX true = x₁
        θX (inr (p , true)) = δ↓ p

        μX : X₁ ((i , x₀) , μ (Pb M X₀) {i = i , x₀} (c , ν) δ)
        μX = fst (contr-center (is-fib-X₂ ((i , x₀) , μ (Pb M X₀) {i = i , x₀} (c , ν) δ) μX-tr θX))

    module _ (X₁ : Rel₁ (Idx↓ M↓)) (X₂ : Rel₂ X₁) (is-fib-X₂ : is-fib₂ X₂) where

      open AlgStruct (Idx↓ M↓) X₁ X₂ is-fib-X₂

      record Hyp (e : AlgEqv X₁) : Set where
        field 

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


    module AlgElim (P : (X₁ : Rel₁ (Idx↓ M↓))
                        (X₂ : Rel₂ X₁)
                        (is-fib-X₂ : is-fib₂ X₂)
                        (e : AlgEqv X₁)
                        (hyp : Hyp X₁ X₂ is-fib-X₂ e)
                        → Type₀)
                   (id* : (X₂ : Rel₂ ↓Rel₁)
                          (is-fib-X₂ : is-fib₂ X₂)
                          (hyp : Hyp ↓Rel₁ X₂ is-fib-X₂ (λ _ → ide _))
                          → P ↓Rel₁ X₂ is-fib-X₂ (λ _ → ide _) hyp) where

      elim : (X₁ : Rel₁ (Idx↓ M↓))
        → (X₂ : Rel₂ X₁) (is-fib-X₂ : is-fib₂ X₂)
        → (e : AlgEqv X₁)
        → (hyp : Hyp X₁ X₂ is-fib-X₂ e)
        → P X₁ X₂ is-fib-X₂ e hyp
      elim X₁ X₂ is-fib-X₂ e hyp = contr-has-section {A = Σ (Rel₁ (Idx↓ M↓)) AlgEqv}
                                                     {B = P'}
                                                     ΣAlgEqv-is-contr _
                                                     id*
                                                     (X₁ , e) X₂ is-fib-X₂ hyp
        where P' : Σ (Rel₁ (Idx↓ M↓)) AlgEqv → Set _
              P' (X₁ , e) = (X₂ : Rel₂ X₁) (is-fib-X₂ : is-fib₂ X₂) (hyp : Hyp X₁ X₂ is-fib-X₂ e)
                            → P X₁ X₂ is-fib-X₂ e hyp
