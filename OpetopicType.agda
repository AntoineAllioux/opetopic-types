{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import SigmaMonad
open import lib.NType2
open import IdentityMonadOver

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
  {-
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
-}
  --
  -- Relative opetopic types
  --
  
  record OpetopicTypeOver {M : 𝕄} (M↓ : 𝕄↓ M) (X : OpetopicType M) : Set₁ where
    coinductive
    field

      Ob↓ : (i : Idx M) → Idx↓ M↓ i → Ob X i → Set
      Hom↓ : OpetopicTypeOver (Slice↓ (Pb↓ M↓ (Ob X) Ob↓)) (Hom X) 

  open OpetopicTypeOver public

  unique-action↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {A : Idx M → Set} (A↓ : (i : Idx M) → Idx↓ M↓ i → A i → Set)
    → {W : Idx (Slice (Pb M A)) → Set}
    → (W↓ : (i : Idx (Slice (Pb M A))) → Idx↓ (Slice↓ (Pb↓ M↓ A A↓)) i → W i → Set)
    → Set
  unique-action↓ {M} M↓ {A} A↓ {W} W↓ = {i : Idx M} (i↓ : Idx↓ M↓ i)
    → {σ : Cns M i} (σ↓ : Cns↓ M↓ i↓ σ)
    → {ν : (p : Pos M σ) → A (Typ M σ p)}
    → (ν↓ : (p : Pos M σ) → A↓ _ (Typ↓ M↓ σ↓ p) (ν p))
    → (a : A i)
    → (w : W ((i , a) , σ , ν))
    → is-contr (Σ (A↓ i i↓ a) (λ a → W↓ _ ((i↓ , a) , σ↓ , ν↓) w))

  record is-fibrant↓ {M : 𝕄} {M↓ : 𝕄↓ M} {X : OpetopicType M} (X↓ : OpetopicTypeOver M↓ X) : Set where
    coinductive
    field

      base-fibrant↓ : unique-action↓ M↓ (Ob↓ X↓) (Ob↓ (Hom↓ X↓))
      hom-fibrant↓ : is-fibrant↓ (Hom↓ X↓)

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

{-
  -- Examples
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

    pd : (x y z : Obj) → Pd (Pb IdMnd (Ob X)) ((ttᵢ , z) , ttᵢ , cst x)
    pd x y z = nd (ttᵢ , cst y) (cst (ttᵢ , cst x))
                  (cst (nd (ttᵢ , (cst x)) (cst (ttᵢ , cst x)) (cst (lf (ttᵢ , x)))))

    pd-cells : {x y z : Obj} (g : Arrow y z) (f : Arrow x y)
        → (p : Posₛ (Pb IdMnd (Ob X)) (pd x y z)) → Ob (Hom X) (Typₛ _ (pd x y z) p)
    pd-cells g f true = g
    pd-cells g f (inr (ttᵢ , true)) = f

    Simplex : {x y z : Obj}
      → (f : Arrow x y) (g : Arrow y z)
      → (h : Arrow x z) → Set
    Simplex {x} {y} {z} f g h = Ob (Hom (Hom X))
      ((((ttᵢ , z) , (ttᵢ , cst x)) , h) ,
        pd x y z ,
        pd-cells g f)


  module _ {X : OpetopicType IdMnd} (Y : OpetopicTypeOver (IdMnd↓ ⊤) X) where

    Obj↓ : Ob X ttᵢ → Set
    Obj↓ x = Ob↓ Y ttᵢ tt x

    Arrow↓ : {x y : Obj X} (x' : Obj↓ x) (y' : Obj↓ y) (f : Arrow X x y) → Set
    Arrow↓ {x} {y} x' y' f = Ob↓ (Hom↓ Y) ((ttᵢ , y) , ttᵢ , cst x) ((tt , y') , ttᵢ , cst x') f

    pd↓ : {x y z : Obj X} (x↓ : Obj↓ x) (y↓ : Obj↓ y) (z↓ : Obj↓ z)
      → Pd↓ (Pb↓ (IdMnd↓ ⊤) (Ob X) (Ob↓ Y)) ((tt , z↓) , ttᵢ , cst x↓) (pd X x y z)
    pd↓ x↓ y↓ z↓ = nd↓ (ttᵢ , cst y↓) (cst (ttᵢ , cst x↓))
                       (cst (nd↓ (ttᵢ , (cst x↓)) (cst (ttᵢ , cst x↓)) (cst (lf↓ (tt , x↓))))) 

    pd-cells↓ : {x y z : Obj X} {g : Arrow X y z} {f : Arrow X x y}
      → {x↓ : Obj↓ x} {y↓ : Obj↓ y} {z↓ : Obj↓ z}
      → (g↓ : Arrow↓ y↓ z↓ g) (f↓ : Arrow↓ x↓ y↓ f)
      → (p : Posₛ (Pb IdMnd (Ob X)) (pd X x y z))
      → Ob↓ (Hom↓ Y) (Typₛ _ (pd X x y z) p) (Typ↓ₛ _ (pd↓ x↓ y↓ z↓) p) (pd-cells X g f p)
    pd-cells↓ g↓ f↓ (inl tt) = g↓
    pd-cells↓ g↓ f↓ (inr (ttᵢ , true)) = f↓

    Simplex↓ : {x y z : Obj X} {x↓ : Obj↓ x} {y↓ : Obj↓ y} {z↓ : Obj↓ z}
      → {f : Arrow X x y} {g : Arrow X y z} {h : Arrow X x z}
      → (f↓ : Arrow↓ x↓ y↓ f) (g↓ : Arrow↓ y↓ z↓ g) (h↓ : Arrow↓ x↓ z↓ h)
      → Simplex X f g h
      → Set
    Simplex↓ {x} {y} {z} {x↓} {y↓} {z↓} {f} {g} {h} f↓ g↓ h↓ α = Ob↓ (Hom↓ (Hom↓ Y))
      ((((ttᵢ , z) , (ttᵢ , cst x)) , h) ,
        pd X x y z ,
        pd-cells X g f)
      (((((tt , z↓) , (ttᵢ , cst x↓)) , h↓) ,
        pd↓ x↓ y↓ z↓ ,
        pd-cells↓ g↓ f↓)) α
-}
