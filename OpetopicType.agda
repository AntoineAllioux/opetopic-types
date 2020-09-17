{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import SigmaMonad

module OpetopicType where

  --
  --  Opetopic Types
  --
  
  record OpetopicType (M : 𝕄) : Set₁ where
    coinductive
    field
    
      Ob : Idx M → Set
      Hom : OpetopicType (Slice (Pb M Ob))

  open OpetopicType public

  --
  --  Fibrancy
  --
  
  unique-action : (M : 𝕄) (A : Idx M → Set)
    → (W : Idx (Slice (Pb M A)) → Set)
    → Set
  unique-action M A W = (f : Idx M) (σ : Cns M f)
    → (ν : (p : Pos M σ) → A (Typ M σ p))
    → is-contr (Σ (A f) (λ a → W ((f , a) , σ , ν)))
    
  record is-fibrant {M : 𝕄} (X : OpetopicType M) : Set where
    coinductive
    field

      base-fibrant : unique-action M (Ob X) (Ob (Hom X))
      hom-fibrant : is-fibrant (Hom X)

  open is-fibrant public

  --
  --  The terminal opetopic type
  --
  
  Terminal : (M : 𝕄) → OpetopicType M
  Ob (Terminal M) = cst ⊤
  Hom (Terminal M) = Terminal (Slice (Pb M (cst ⊤)))

  --
  --  The opetopic type associated to a monad over
  --
  
  ↓-to-OpType : (M : 𝕄) (M↓ : 𝕄↓ M)
    → OpetopicType M
  Ob (↓-to-OpType M M↓) = Idx↓ M↓ 
  Hom (↓-to-OpType M M↓) =
    ↓-to-OpType (Slice (Pb M (Idx↓ M↓)))
                       (Slice↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)))


  --
  --  Examples of Opetopic shapes
  --
  
  module _ (X : OpetopicType IdMnd) where

    Obj : Set
    Obj = Ob X ttᵢ

    Arrow : (x y : Obj) → Set
    Arrow x y = Ob (Hom X) ((ttᵢ , y) , (ttᵢ , cst x))

    NullHomotopy : {x : Obj} (f : Arrow x x) → Set
    NullHomotopy {x} f = Ob (Hom (Hom X))
      ((((ttᵢ , x) , (ttᵢ , cst x)) , f) , lf (ttᵢ , x) , ⊥-elim) 

    Disc : {x y : Obj}
      → (f : Arrow x y) (g : Arrow x y)
      → Set
    Disc {x} {y} f g = Ob (Hom (Hom X))
      ((((ttᵢ , y) , (ttᵢ , cst x)) , g) ,
        (nd (ttᵢ , cst x) (cst (ttᵢ , (cst x))) (cst (lf (ttᵢ , x)))) , (λ { true → f }))

    Simplex : {x y z : Obj}
      → (f : Arrow x y) (g : Arrow y z)
      → (h : Arrow x z) → Set
    Simplex {x} {y} {z} f g h = Ob (Hom (Hom X))
      ((((ttᵢ , z) , (ttᵢ , cst x)) , h) ,
        (nd (ttᵢ , cst y) (cst (ttᵢ , cst x)) (cst
          (nd (ttᵢ , (cst x)) (cst (ttᵢ , cst x)) (cst (lf (ttᵢ , x)))))) ,
        (λ { true → g ;
             (inr (ttᵢ , true)) → f }))

  --
  -- Relative opetopic types
  --
  
  record OpetopicTypeOver {M : 𝕄} (M↓ : 𝕄↓ M) (X : OpetopicType M) : Set₁ where
    coinductive
    field

      Ob↓ : (i : Idx M) → Idx↓ M↓ i → Ob X i → Set
      Hom↓ : OpetopicTypeOver (Slice↓ (Pb↓ M↓ (Ob X) Ob↓)) (Hom X) 

  open OpetopicTypeOver public

  -- Have to transport by an equivalence for this ...
  -- ΣO : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → (X : OpetopicType M)
  --   → OpetopicTypeOver M↓ X
  --   → OpetopicType (ΣM M M↓)
  -- Ob (ΣO M↓ X Y) (i , j) = Σ (Ob X i) (Ob↓ Y i j)
  -- Hom (ΣO {M} M↓ X Y) = {!!}

  --   where CH : OpetopicType (ΣM (Slice (Pb M (Ob X))) (Slice↓ (Pb↓ M↓ (Ob X) (Ob↓ Y))))
  --         CH = ΣO {M = Slice (Pb M (Ob X))} (Slice↓ (Pb↓ M↓ (Ob X) (Ob↓ Y))) (Hom X) (Hom↓ Y) 
