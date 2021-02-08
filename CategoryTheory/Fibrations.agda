{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import OpetopicType
open import IdentityMonad
open import IdentityMonadOver

module CategoryTheory.Fibrations where

  module _ {X : OpetopicType IdMnd} (X↓ : OpetopicTypeOver (IdMnd↓ ⊤) X) where

    is-cartesian : {x y : Obj X} {x' : Obj↓ X↓ x} {y' : Obj↓ X↓ y} {f : Arrow X x y} (f' : Arrow↓ X↓ x' y' f) → Set
    is-cartesian {x} {y} {x'} {y'} {f} f' = (z : Obj X) (z' : Obj↓ X↓ z)
      → (g : Arrow X z y) (g' : Arrow↓ X↓ z' y' g) (h : Arrow X z x)
      → (fill : Simplex X h f g)
      → is-contr (Σ (Arrow↓ X↓ z' x' h) λ h' →
                     Simplex↓ X↓ h' f' g' fill)

    is-cocartesian : {x y : Obj X} {x' : Obj↓ X↓ x} {y' : Obj↓ X↓ y} {f : Arrow X x y} (f' : Arrow↓ X↓ x' y' f) → Set
    is-cocartesian {x} {y} {x'} {y'} {f} f' = (z : Obj X) (z' : Obj↓ X↓ z)
      → (g : Arrow X x z) (g' : Arrow↓ X↓ x' z' g) (h : Arrow X y z)
      → (fill : Simplex X f h g)
      → is-contr (Σ (Arrow↓ X↓ y' z' h) λ h' →
                     Simplex↓ X↓ f' h' g' fill)
                     
    is-fibration : Set
    is-fibration = {x y : Obj X} (f : Arrow X x y)
      → (y' : Obj↓ X↓ y)
      → Σ (Obj↓ X↓ x) λ x' →
        Σ (Arrow↓ X↓ x' y' f) λ f' →
          is-cartesian f'

    is-opfibration : Set
    is-opfibration = {x y : Obj X} (f : Arrow X x y)
      → (x' : Obj↓ X↓ x)
      → Σ (Obj↓ X↓ y) λ y' → 
        Σ (Arrow↓ X↓ x' y' f) λ f' →
          is-cocartesian f'

