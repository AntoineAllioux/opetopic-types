{-# OPTIONS --without-K --rewriting --allow-unsolved-meta #-}

open import HoTT
open import OpetopicType
open import Monad
open import IdentityMonad
open import Utils
open import CategoryTheory.InftyCategories

module CategoryTheory.Interval where

  𝟚-op-type : OpetopicType IdMnd
  Ob 𝟚-op-type _ = Bool
  Ob (Hom 𝟚-op-type) ((ttᵢ , true) , ttᵢ , ν) = ⊤
  Ob (Hom 𝟚-op-type) ((ttᵢ , false) , ttᵢ , ν) with ν ttᵢ
  ... | false = ⊤
  ... | true = ⊥
  Hom (Hom 𝟚-op-type) = Terminal _

  
  𝟚-op-type-is-fibrant : is-fibrant (Hom 𝟚-op-type)
  base-fibrant 𝟚-op-type-is-fibrant ((ttᵢ , true) , ttᵢ , ν) σ ν' = has-level-in ((tt , tt) , λ { (tt , tt) → idp })
  base-fibrant 𝟚-op-type-is-fibrant ((ttᵢ , false) , _ , _) (lf .(ttᵢ , false)) c = has-level-in ((tt , tt) , λ { (tt , tt) → idp })
  base-fibrant 𝟚-op-type-is-fibrant = {!!}
  hom-fibrant 𝟚-op-type-is-fibrant = Terminal-is-fibrant _

  𝟚 : ∞-category
  𝟚 = 𝟚-op-type , 𝟚-op-type-is-fibrant
