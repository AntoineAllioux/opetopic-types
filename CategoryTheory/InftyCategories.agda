{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import HoTT
open import OpetopicType
open import Monad
open import IdentityMonad
open import IdentityMonadOver
open import AlgEqvElim

module CategoryTheory.InftyCategories where

  ∞-category : Set (lsucc lzero)
  ∞-category = Σ (OpetopicType IdMnd) (is-fibrant ∘ Hom)

  ∞-category↓ : (C : ∞-category) → Set (lsucc lzero)
  ∞-category↓ C = Σ (OpetopicTypeOver (IdMnd↓ ⊤) (fst C)) (is-fibrant↓ ∘ Hom↓)

  module _ (C : ∞-category) where


    open import SliceUnfold IdMnd
    open Stuff (Slc₁ (Ob (fst C)))

    private
      X = fst C
      fib = snd C

    compₒ : {x y z : Obj X} (g : Arrow X y z) (f : Arrow X x y) → Arrow X x z
    compₒ {x} {y} {z} g f = AlgStruct.μX IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib) _ _ _ _ _ g (cst f)

    fillₒ : {x y z : Obj X} (g : Arrow X y z) (f : Arrow X x y) → Simplex X f g (compₒ g f)
    fillₒ {x} {y} {z} g f = {! AlgStruct.μX-fill IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib) _ _ _ _ _ g (cst f) !}

    id : (x : Obj X) → Arrow X x x
    id x = AlgStruct.ηX IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib) ttᵢ x

    unit-rₒ : {x y : Obj X} (f : Arrow X x y) → compₒ f (id x) == f
    unit-rₒ f = AlgStruct.μX-unit-r IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib) (Ob (Hom (Hom ( Hom X)))) (base-fibrant (hom-fibrant fib)) _ _ _ _ f

    unit-lₒ : {x y : Obj X} (f : Arrow X x y) → compₒ (id y) f == f
    unit-lₒ f = AlgStruct.μX-unit-l IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib) (Ob (Hom (Hom ( Hom X)))) (base-fibrant (hom-fibrant fib)) _ _ _ (cst f)

    assocₒ : {x y z t : Obj X} (h : Arrow X z t) (g : Arrow X y z) (f : Arrow X x y) → compₒ (compₒ h g) f == compₒ h (compₒ g f)
    assocₒ h g f = ! (AlgStruct.μX-assoc IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib) _ (base-fibrant (hom-fibrant fib))  _ _  _ _ _  h (cst g) _ (cst f))

    record is-isoₒ {x y : Obj X} (f : Arrow X x y) : Set where
      constructor mk-isoₒ
      field
        g   : Arrow X y x
        f-g : compₒ f g == (id y) 
        g-f : compₒ g f == (id x)

    is-isoₒ= : {x y : Obj X}
      → {f : Arrow X x y} 
      → {g g₁ : Arrow X y x}
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
    isoₒ x y = Σ (Arrow X x y) is-isoₒ
    
    id-is-isoₒ : (x : Obj X) → is-isoₒ (id x)
    is-isoₒ.g (id-is-isoₒ x) = id _
    is-isoₒ.f-g (id-is-isoₒ x) = unit-rₒ _
    is-isoₒ.g-f (id-is-isoₒ x) = unit-rₒ _

    id-to-isoₒ : (x y : Obj X)
      → x == y
      → isoₒ x y
    id-to-isoₒ x _ idp = id x , id-is-isoₒ x 

    is-complete : Set
    is-complete = {x y : Obj X}
      → is-equiv (id-to-isoₒ x y)


  ∞-ucategory : Set (lsucc lzero)
  ∞-ucategory = Σ ∞-category is-complete 

  
  
