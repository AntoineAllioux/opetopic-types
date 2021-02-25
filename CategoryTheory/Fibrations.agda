{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import OpetopicType
open import IdentityMonad
open import IdentityMonadOver
open import CategoryTheory.InftyCategories

module CategoryTheory.Fibrations where

  module _ {X : OpetopicType IdMnd} (X↓ : OpetopicTypeOver (IdMnd↓ ⊤) X) where
  
    open IdentityCells↓ X↓
    
    is-cartesian : {x y : Obj} {x' : Obj↓ x} {y' : Obj↓ y} {f : Arrow x y} (f' : Arrow↓ x' y' f) → Set
    is-cartesian {x} {y} {x'} {y'} {f} f' = (z : Obj) (z' : Obj↓ z)
      → (g : Arrow z y) (g' : Arrow↓ z' y' g) (h : Arrow z x)
      → (fill : Simplex h f g)
      → is-contr (Σ (Arrow↓ z' x' h) λ h' →
                     Simplex↓ h' f' g' fill)

    is-cocartesian : {x y : Obj} {x' : Obj↓ x} {y' : Obj↓ y} {f : Arrow x y} (f' : Arrow↓ x' y' f) → Set
    is-cocartesian {x} {y} {x'} {y'} {f} f' = (z : Obj) (z' : Obj↓ z)
      → (g : Arrow x z) (g' : Arrow↓ x' z' g) (h : Arrow y z)
      → (fill : Simplex f h g)
      → is-contr (Σ (Arrow↓ y' z' h) λ h' →
                     Simplex↓ f' h' g' fill)
                     
    is-fibration : Set
    is-fibration = {x y : Obj} (f : Arrow x y)
      → (y' : Obj↓ y)
      → Σ (Obj↓ x) λ x' →
        Σ (Arrow↓ x' y' f) λ f' →
          is-cartesian f'

    is-opfibration : Set
    is-opfibration = {x y : Obj} (f : Arrow x y)
      → (x' : Obj↓ x)
      → Σ (Obj↓ y) λ y' → 
        Σ (Arrow↓ x' y' f) λ f' →
          is-cocartesian f'

