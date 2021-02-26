{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import HoTT
open import OpetopicType
open import Monad
open import IdentityMonad
open import IdentityMonadOver
open import Algebras
open import AlgebrasOver

open import Pb
open import MonadOver

module CategoryTheory.InftyCategories where

  ∞-category : Set (lsucc lzero)
  ∞-category = Σ (OpetopicType IdMnd) (is-fibrant ∘ Hom)

  ∞-category↓ : (C : ∞-category) → Set (lsucc lzero)
  ∞-category↓ C = Σ (OpetopicTypeOver (IdMnd↓ ⊤) (fst C)) (is-fibrant↓ ∘ Hom↓)

  module IdentityCells (X : OpetopicType IdMnd) where
    Obj : Set
    Obj = Ob X ttᵢ

    Arrow : (x y : Obj) → Set
    Arrow x y = Ob (Hom X) ((ttᵢ , y) , (ttᵢ , cst x))

    Simplex : {x y z : Obj}
      → (f : Arrow x y) (g : Arrow y z)
      → (h : Arrow x z) → Set
    Simplex {x} {y} {z} f g h = Ob (Hom (Hom X))
      ((((ttᵢ , z) , (ttᵢ , cst x)) , h) ,
        μX-tr ,
        θX)
      where open SourceHelper (Pb IdMnd (Ob X)) (Ob (Hom X))
                              (ttᵢ , z) (ttᵢ , cst y) (cst (ttᵢ , cst x)) g (cst f)

  module IdentityCells↓ {X : OpetopicType IdMnd} (X↓ : OpetopicTypeOver (IdMnd↓ ⊤) X) where

    open IdentityCells X public
    
    Obj↓ : Ob X ttᵢ → Set
    Obj↓ x = Ob↓ X↓ ttᵢ tt x

    Arrow↓ : {x y : Obj} (x' : Obj↓ x) (y' : Obj↓ y) (f : Arrow x y) → Set
    Arrow↓ {x} {y} x' y' f = Ob↓ (Hom↓ X↓) ((ttᵢ , y) , ttᵢ , cst x) ((tt , y') , ttᵢ , cst x') f

    Simplex↓ : {x y z : Obj} {x↓ : Obj↓ x} {y↓ : Obj↓ y} {z↓ : Obj↓ z}
      → {f : Arrow x y} {g : Arrow y z} {h : Arrow x z}
      → (f↓ : Arrow↓ x↓ y↓ f) (g↓ : Arrow↓ y↓ z↓ g) (h↓ : Arrow↓ x↓ z↓ h)
      → Simplex f g h
      → Set
    Simplex↓ {x} {y} {z} {x↓} {y↓} {z↓} {f} {g} {h} f↓ g↓ h↓ α = Ob↓ (Hom↓ (Hom↓ X↓))
      ((((ttᵢ , z) , (ttᵢ , cst x)) , h) ,
        μX-tr ,
        θX)
        ((((tt , z↓) , (ttᵢ , cst x↓)) , h↓) ,
        μX-tr↓ ,
        θX↓) α
      where open SourceHelper↓ (Pb↓ (IdMnd↓ ⊤) (Ob X) (Ob↓ X↓)) (Ob↓ (Hom↓ X↓))
                               (tt , z↓) (ttᵢ , cst y↓) (cst (ttᵢ , cst x↓)) g↓ (cst f↓) 
 
  module _ (C : ∞-category) where

    private
      X = fst C
      fib = snd C

    open import SliceUnfold IdMnd
    open IdentityCells X
    
    open AlgStruct IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib)    

    compₒ : {x y z : Obj} (g : Arrow y z) (f : Arrow x y) → Arrow x z
    compₒ {x} {y} {z} g f = μX _ _ _ _ _ g (cst f)

    fillₒ : {x y z : Obj} (g : Arrow y z) (f : Arrow x y) → Simplex f g (compₒ g f)
    fillₒ {x} {y} {z} g f =  μX-fill _ _ _ _ _ g (cst f) 

    id : (x : Obj) → Arrow x x
    id x = ηX ttᵢ x

    unit-rₒ : {x y : Obj} (f : Arrow x y) → compₒ f (id x) == f
    unit-rₒ f = μX-unit-r (Ob (Hom (Hom ( Hom X)))) (base-fibrant (hom-fibrant fib)) _ _ _ _ f

    unit-lₒ : {x y : Obj} (f : Arrow x y) → compₒ (id y) f == f
    unit-lₒ f = μX-unit-l (Ob (Hom (Hom ( Hom X)))) (base-fibrant (hom-fibrant fib)) _ _ _ (cst f)

    assocₒ : {x y z t : Obj} (h : Arrow z t) (g : Arrow y z) (f : Arrow x y) → compₒ (compₒ h g) f == compₒ h (compₒ g f)
    assocₒ h g f = ! (μX-assoc _ (base-fibrant (hom-fibrant fib))  _ _  _ _ _  h (cst g) _ (cst f))

    record is-isoₒ {x y : Obj} (f : Arrow x y) : Set where
      constructor mk-isoₒ
      field
        g   : Arrow y x
        f-g : compₒ f g == (id y) 
        g-f : compₒ g f == (id x)

    is-isoₒ= : {x y : Obj}
      → {f : Arrow x y} 
      → {g g₁ : Arrow y x}
      → (g=g₁ : g == g₁)
      → {f-g : compₒ f g == id y}
      → {f-g₁ : compₒ f g₁ == id y}
      → (f-g=f-g₁ : f-g == f-g₁ [ (λ g → compₒ f g == id y) ↓ g=g₁ ])
      → {g-f : compₒ g f == id x}
      → {g-f₁ : compₒ g₁ f == id x}
      → (g-f=g-f₁ : g-f == g-f₁ [ (λ g → compₒ g f == id x) ↓ g=g₁ ])
      → mk-isoₒ g f-g g-f == mk-isoₒ g₁ f-g₁ g-f₁
    is-isoₒ= idp idp idp = idp

    isoₒ : (x y : Ob X ttᵢ) → Set
    isoₒ x y = Σ (Arrow x y) is-isoₒ
    
    id-is-isoₒ : (x : Obj) → is-isoₒ (id x)
    is-isoₒ.g (id-is-isoₒ x) = id _
    is-isoₒ.f-g (id-is-isoₒ x) = unit-rₒ _
    is-isoₒ.g-f (id-is-isoₒ x) = unit-rₒ _

    id-to-isoₒ : (x y : Obj)
      → x == y
      → isoₒ x y
    id-to-isoₒ x _ idp = id x , id-is-isoₒ x 

    is-complete : Set
    is-complete = {x y : Obj}
      → is-equiv (id-to-isoₒ x y)


  ∞-ucategory : Set (lsucc lzero)
  ∞-ucategory = Σ ∞-category is-complete 


  module _ {C : ∞-category} (C↓ : ∞-category↓ C) where

    private
      X = fst C
      fib = snd C
      X↓ = fst C↓
      fib↓ = snd C↓

    open IdentityCells↓ X↓
    open AlgStruct↓ (IdMnd↓ ⊤) (Ob↓ X↓) (Ob↓ (Hom↓ X↓)) (Ob↓ (Hom↓ (Hom↓ X↓))) (base-fibrant fib) (base-fibrant↓ fib↓)

    comp↓ : {x y z : Obj} {x↓ : Obj↓ x} {y↓ : Obj↓ y} {z↓ : Obj↓ z}
      → {g : Arrow y z} {f : Arrow x y}
      → (g↓ : Arrow↓ y↓ z↓ g) (f↓ : Arrow↓ x↓ y↓ f) 
      → Arrow↓ x↓ z↓ (compₒ C g f)
    comp↓ {g = g} {f = f} g↓ f↓ = μX↓ _ _ _ _ _ g↓ (cst f↓)

    fill↓ : {x y z : Obj} {x↓ : Obj↓ x} {y↓ : Obj↓ y} {z↓ : Obj↓ z}
      → {g : Arrow y z} {f : Arrow x y}
      → (g↓ : Arrow↓ y↓ z↓ g) (f↓ : Arrow↓ x↓ y↓ f) 
      → Simplex↓ f↓ g↓ (comp↓ g↓ f↓) (fillₒ C g f)
    fill↓ {g = g} {f = f} g↓ f↓ = μX-fill↓ _ _ _ _ _ g↓ (cst f↓)

