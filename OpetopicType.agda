{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import SigmaMonad
open import lib.NType2

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
  {-# ETA is-fibrant #-}

  is-fibrant= : {M : 𝕄} {X : OpetopicType M}
    → {base-fibrant base-fibrant' : unique-action M (Ob X) (Ob (Hom X))}
    → (base-fibrant= : base-fibrant == base-fibrant')
    → {hom-fibrant hom-fibrant' : is-fibrant (Hom X)}
    → (hom-fibrant= : hom-fibrant == hom-fibrant')
    → _==_ {A = is-fibrant X} record { base-fibrant = base-fibrant ; hom-fibrant = hom-fibrant }
       record { base-fibrant = base-fibrant' ; hom-fibrant = hom-fibrant' }
  is-fibrant= base-fibrant= hom-fibrant= =
    ap (λ { (base-fibrant , hom-fibrant) → record { base-fibrant = base-fibrant ; hom-fibrant = hom-fibrant } })
      (pair×= base-fibrant= hom-fibrant=)

  {-# TERMINATING #-}
  is-fibrant-is-prop : {M : 𝕄} (X : OpetopicType M) → is-prop (is-fibrant X)
  is-fibrant-is-prop X = all-paths-is-prop λ x y → is-fibrant= (prop-path (Π-level (λ _ → Π-level λ _ → Π-level λ _ → has-level-is-prop)) _ _) (prop-path (is-fibrant-is-prop (Hom X)) _ _)
  
  open is-fibrant public

  --
  --  The terminal opetopic type
  --

  Terminal : (M : 𝕄) → OpetopicType M
  Ob (Terminal M) = cst ⊤
  Hom (Terminal M) = Terminal (Slice (Pb M (cst ⊤)))

  Terminal-is-fibrant : (M : 𝕄) → is-fibrant (Terminal M)
  base-fibrant (Terminal-is-fibrant M) f σ ν = Σ-level Unit-level λ _ → Unit-level
  hom-fibrant (Terminal-is-fibrant M) = Terminal-is-fibrant _

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
    Arrow x y = Ob (Hom X) ((ttᵢ , y) , (ttᵢ , η-dec IdMnd (Ob X) x))

    NullHomotopy : {x : Obj} (f : Arrow x x) → Set
    NullHomotopy {x} f = Ob (Hom (Hom X))
      ((((ttᵢ , x) , (ttᵢ , η-dec IdMnd (Ob X) x)) , f) , lf (ttᵢ , x) , ⊥-elim) 

    --
    --  These need to be fixed to use η-decorations ...
    -- 

    -- Disc : {x y : Obj}
    --   → (f : Arrow x y) (g : Arrow x y)
    --   → Set
    -- Disc {x} {y} f g = Ob (Hom (Hom X))
    --   ((((ttᵢ , y) , (ttᵢ , cst x)) , g) ,
    --     (nd (ttᵢ , cst x) (cst (ttᵢ , (cst x))) (cst (lf (ttᵢ , x)))) , (λ { true → f }))

    -- Simplex : {x y z : Obj}
    --   → (f : Arrow x y) (g : Arrow y z)
    --   → (h : Arrow x z) → Set
    -- Simplex {x} {y} {z} f g h = Ob (Hom (Hom X))
    --   ((((ttᵢ , z) , (ttᵢ , cst x)) , h) ,
    --     (nd (ttᵢ , cst y) (cst (ttᵢ , cst x)) (cst
    --       (nd (ttᵢ , (cst x)) (cst (ttᵢ , cst x)) (cst (lf (ttᵢ , x)))))) ,
    --     (λ { true → g ;
    --          (inr (ttᵢ , true)) → f }))

  --
  -- Relative opetopic types
  --
  
  record OpetopicTypeOver {M : 𝕄} (M↓ : 𝕄↓ M) (X : OpetopicType M) : Set₁ where
    coinductive
    field

      Ob↓ : (i : Idx M) → Idx↓ M↓ i → Ob X i → Set
      Hom↓ : OpetopicTypeOver (Slice↓ (Pb↓ M↓ (Ob X) Ob↓)) (Hom X) 

  open OpetopicTypeOver public

  action↓ : {M : 𝕄} (M↓ : 𝕄↓ M) (A : Idx M → Set)
    → (W : Idx (Slice (Pb M A)) → Set)
    → (A↓ : {i : Idx M} (j : Idx↓ M↓ i) → A i → Set)
    → Set
  action↓ {M} M↓ A W A↓ = {f : Idx M} {σ : Cns M f}
    → {ν : (p : Pos M σ) → A (Typ M σ p)}
    → {τ : A f}
    → (θ : W ((f , τ) , σ , ν))
    → (f↓ : Idx↓ M↓ f) (σ↓ : Cns↓ M↓ f↓ σ)
    → (ν↓ : (p : Pos M σ) → A↓ (Typ↓ M↓ σ↓ p) (ν p))
    → A↓ f↓ τ

  unique-action↓ : {M : 𝕄} (M↓ : 𝕄↓ M) {A : Idx M → Set}
    → {W : Idx (Slice (Pb M A)) → Set}
    → (A↓ : (i : Idx M) (j : Idx↓ M↓ i) → A i → Set)
    → (W↓ : (i : Idx (Slice (Pb M A))) (j : Idx↓ (Slice↓ (Pb↓ M↓ A A↓)) i) → W i → Set)
    → Set
  unique-action↓ {M} M↓ {A} {W} A↓ W↓ = {f : Idx M} {σ : Cns M f}
    → {ν : (p : Pos M σ) → A (Typ M σ p)}
    → {τ : A f}
    → (θ : W ((f , τ) , σ , ν))
    → (f↓ : Idx↓ M↓ f) (σ↓ : Cns↓ M↓ f↓ σ)
    → (ν↓ : (p : Pos M σ) → A↓ _ (Typ↓ M↓ σ↓ p) (ν p))
    → is-contr (Σ (A↓ _ f↓ τ) λ τ → W↓ _ ((f↓ , τ) , σ↓ , ν↓) θ)

  record is-fibrant↓ {M : 𝕄} {M' : 𝕄↓ M} {X : OpetopicType M} (Y : OpetopicTypeOver M' X) : Set where
    coinductive
    field

      base-fibrant↓ : unique-action↓ M' (Ob↓ Y) (Ob↓ (Hom↓ Y))
      hom-fibrant↓ : is-fibrant↓ (Hom↓ Y)

  open is-fibrant↓ public

  -- Have to transport by an equivalence for this ...
  -- ΣO : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → (X : OpetopicType M)
  --   → OpetopicTypeOver M↓ X
  --   → OpetopicType (ΣM M M↓)
  -- Ob (ΣO M↓ X Y) (i , j) = Σ (Ob X i) (Ob↓ Y i j)
  -- Hom (ΣO {M} M↓ X Y) = {!!}

  --   where CH : OpetopicType (ΣM (Slice (Pb M (Ob X))) (Slice↓ (Pb↓ M↓ (Ob X) (Ob↓ Y))))
  --         CH = ΣO {M = Slice (Pb M (Ob X))} (Slice↓ (Pb↓ M↓ (Ob X) (Ob↓ Y))) (Hom X) (Hom↓ Y) 
