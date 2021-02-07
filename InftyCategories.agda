{-# OPTIONS --rewriting --without-K #-}

open import HoTT
open import OpetopicType
open import Monad
open import IdentityMonad
open import AlgEqvElim

module InftyCategories where

  ∞-category : Set (lsucc lzero)
  ∞-category = Σ (OpetopicType IdMnd) (is-fibrant ∘ Hom)
{-
  record ∞-category : Set (lsucc lzero) where
    field
      X : OpetopicType IdMnd
      X-is-fib : is-fibrant (Hom X)
  -}  

  module _ (C : ∞-category) where


    open import SliceUnfold IdMnd
    open Stuff (Slc₁ (Ob (fst C)))
    
    X = fst C
    fib = snd C

    compₒ : {x y z : Obj X} (g : Arrow X y z) (f : Arrow X x y) → Arrow X x z
    compₒ {x} {y} {z} g f = AlgStruct.μX IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib) _ _ _ _ _ g (cst f)

    id : (x : Obj X) → Arrow X x x
    id x = AlgStruct.ηX IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib) ttᵢ x

    unit-rₒ : {x y : Obj X} (f : Arrow X x y) → compₒ f (id x) == f
    unit-rₒ f = AlgStruct.μX-unit-r IdMnd (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant fib) (Ob (Hom (Hom ( Hom X)))) (base-fibrant (hom-fibrant fib)) _ _ _ _ f

    record is-isoₒ {x y : Obj X} (f : Arrow X x y) : Set where
      constructor mk-isoₒ
      field
        g   : Arrow X y x
        f-g : compₒ f g == (id y) 
        g-f : compₒ g f == (id x) 

    isoₒ : (x y : Ob X ttᵢ) → Set
    isoₒ x y = Σ (Arrow X x y) is-isoₒ
    

    id-is-isoₒ : (x : Obj X) → is-isoₒ (id x)
    is-isoₒ.g (id-is-isoₒ x) = id _
    is-isoₒ.f-g (id-is-isoₒ x) = unit-rₒ _
    is-isoₒ.g-f (id-is-isoₒ x) = unit-rₒ _

    id-to-isoₒ : {x y : Obj X}
      → x == y
      → isoₒ x y
    id-to-isoₒ {x} idp = id x , id-is-isoₒ x 


    is-complete : Set
    is-complete = {x y : Obj X}
      → is-equiv (id-to-isoₒ {x} {y})


  ∞-ucategory : Set (lsucc lzero)
  ∞-ucategory = Σ ∞-category is-complete 

  
