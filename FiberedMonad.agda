{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Universe
open import Util

module FiberedMonad where

  postulate

    𝕄 : Set

    Idx : 𝕄 → Set
    Cns : (M : 𝕄) (i : Idx M) (P : 𝕌) (ρ : El P → Idx M) → Set 

    η : (M : 𝕄) (i : Idx M) → Cns M i ⊤ₛ (cst i)

    μ : (M : 𝕄) (i : Idx M)
      → (P : 𝕌) (ρ : El P → Idx M) (c : Cns M i P ρ)
      → (Q : El P → 𝕌) (σ : (p : El P) → El (Q p) → Idx M)
      → (d : (p : El P) → Cns M (ρ p) (Q p) (σ p))
      → Cns M i (Σₛ P Q) (uncurryₛ σ)

    -- Monad laws
    μ-unit-right : (M : 𝕄) (i : Idx M)
      → (P : 𝕌) (ρ : El P → Idx M) (c : Cns M i P ρ)
      → μ M i P ρ c (cst ⊤ₛ) (λ p → cst (ρ p)) (λ p → η M (ρ p)) ↦ c 
    {-# REWRITE μ-unit-right #-}

    μ-unit-left : (M : 𝕄) (i : Idx M)
      → (Q : El ⊤ₛ → 𝕌) (σ : (u : El ⊤ₛ) → El (Q u) → Idx M)
      → (d : (u : El ⊤ₛ) → Cns M i (Q u) (σ u))
      → μ M i ⊤ₛ (cst i) (η M i) Q σ d ↦ d ttₛ 
    {-# REWRITE μ-unit-left #-}

    μ-assoc : (M : 𝕄) (i : Idx M)
      → (P : 𝕌) (ρ : El P → Idx M) (c : Cns M i P ρ)
      → (Q : El P → 𝕌) (σ : (p : El P) → El (Q p) → Idx M)
      → (d : (p : El P) → Cns M (ρ p) (Q p) (σ p))
      → (R : El (Σₛ P Q) → 𝕌)
      → (τ : (p : El (Σₛ P Q)) → El (R p) → Idx M)
      → (e : (p : El (Σₛ P Q)) → Cns M (uncurryₛ σ p) (R p) (τ p))
      → μ M i (Σₛ P Q) (uncurryₛ σ) (μ M i P ρ c Q σ d) R τ e
          ↦ μ M i P ρ c (λ p → Σₛ (Q p) (λ q → R (prₛ P Q p q)))
                        (λ p qr → τ (prₛ P Q p (fstₛ (Q p) (λ q → R (prₛ P Q p q)) qr)) (sndₛ (Q p) (λ q → R (prₛ P Q p q)) qr))
                        (λ p → μ M (ρ p) (Q p) (λ q → σ p q) (d p) (λ q → R (prₛ P Q p q)) (λ q → τ (prₛ P Q p q)) (λ q → e (prₛ P Q p q)))
    {-# REWRITE μ-assoc #-}

  Idxₛ : (M : 𝕄) → Set
  Idxₛ M = Σ (Idx M) (λ i → Σ 𝕌 (λ P → Σ (El P → Idx M) λ ρ → Cns M i P ρ))

  data Cnsₛ (M : 𝕄) : Idxₛ M → (Q : 𝕌) → (θ : El Q → Idxₛ M) → Set where

    lf : (i : Idx M) → Cnsₛ M (i , ⊤ₛ , cst i , η M i) ⊥ₛ (⊥ₛ-elim (Idxₛ M))
    
    nd : (i : Idx M) (P : 𝕌) (ρ : El P → Idx M) (c : Cns M i P ρ)
      → (Q : El P → 𝕌) (σ : (p : El P) → El (Q p) → Idx M)
      → (d : (p : El P) → Cns M (ρ p) (Q p) (σ p))
      → (R : El P → 𝕌) (τ : (p : El P) → El (R p) → Idxₛ M)
      → (e : (p : El P) → Cnsₛ M (ρ p , Q p , σ p , d p) (R p) (τ p))
      → Cnsₛ M (i , Σₛ P Q , uncurryₛ σ , μ M i P ρ c Q σ d) (⊤ₛ ⊔ₛ (Σₛ P R))
        (⊔ₛ-rec ⊤ₛ (Σₛ P R) (cst (i , Σₛ P Q , uncurryₛ σ , μ M i P ρ c Q σ d)) (uncurryₛ τ))

  --
  --  I see.  We need the laws for μ at this point.
  --
  
  ηₛ : (M : 𝕄) (i : Idxₛ M) → Cnsₛ M i ⊤ₛ (cst i)
  ηₛ M (i , P , ρ , c) =
    let η-dec p = η M (ρ p)
        lf-dec p = lf (ρ p) 
    in nd i P ρ c (cst ⊤ₛ) (λ p → cst (ρ p)) η-dec
                  (cst ⊥ₛ) (cst (⊥ₛ-elim (Idxₛ M))) lf-dec  

  -- μ : (M : 𝕄) (i : Idx M)
  --   → (P : Set) (τ₀ : P → Idx M) (c : Cns M i P τ₀)
  --   → (Q : P → Set) (τ₁ : (p : P) → Q p → Idx M)
  --   → (d : (p : P) → Cns M (τ₀ p) (Q p) (τ₁ p))
  --   → Cns M i (Σₛ P Q) (uncurryₛ τ₁)

  -- So, this means the only thing left to do is to implement η and μ
  -- for the slice.  Wacky.


