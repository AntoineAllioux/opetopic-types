{-# OPTIONS --rewriting --without-K #-}

open import CategoryTheory.InftyCategories
open import CategoryTheory.Interval
open import CategoryTheory.Fibrations
open import OpetopicType
open import IdentityMonad
open import IdentityMonadOver
open import HoTT
open import AlgebrasOver
open import Monad
open import MonadOver
open import Pb

module CategoryTheory.Functors where

  

  module _ (C↓ : ∞-category↓ 𝟚)
           (fib : is-fibration (fst C↓))
           (opfib : is-opfibration (fst C↓)) where
    
    private
      X↓ = fst C↓
      fib↓ = snd C↓

    open IdentityCells↓ X↓
    open AlgStruct↓ (IdMnd↓ ⊤)
                    (Ob↓ X↓) (Ob↓ (Hom↓ X↓)) (Ob↓ (Hom↓ (Hom↓ X↓)))
                    (base-fibrant 𝟚-op-type-is-fibrant) (base-fibrant↓ fib↓)


    F : Ob↓ X↓ ttᵢ tt false → Ob↓ X↓ ttᵢ tt true
    F x = fst (opfib tt x)

    G : Ob↓ X↓ ttᵢ tt true → Ob↓ X↓ ttᵢ tt false
    G x = fst (fib tt x)

    adj : (x : Ob↓ X↓ ttᵢ tt false)
      → (y : Ob↓ X↓ ttᵢ tt true)
      → Arrow↓ x (G y) tt
        ≃ Arrow↓ (F x) y tt
    adj x y = g , is-eq g h g-h h-g
      where g-aux : (f : Arrow↓ x (G y) tt)
                  → is-contr (Σ (Arrow↓ (F x) y tt) λ p →
                                 Simplex↓ (fst (snd (opfib tt x))) p
                                 (comp↓ {C = 𝟚} C↓ (fst (snd (fib tt y))) f) tt)
            g-aux f =
              let x→Fx : Arrow↓ x (F x) tt
                  x→Fx = fst (snd (opfib tt x))

                  cocart : is-cocartesian X↓ x→Fx
                  cocart = snd (snd (opfib tt x))

                  Gy→y : Arrow↓ (G y) y tt
                  Gy→y = fst (snd (fib tt y))
 
                  h : Arrow↓ x y tt
                  h = comp↓ {C = 𝟚} C↓ Gy→y f 

              in cocart true y tt h tt tt

            g : Arrow↓ x (G y) tt → Arrow↓ (F x) y tt
            g = fst ∘ contr-center ∘ g-aux

            h-aux : (f : Arrow↓ (F x) y tt)
              → is-contr (Σ (Arrow↓ x (G y) tt) λ f' →
                            Simplex↓ f' (fst (snd (fib tt y)))
                                     (comp↓ {C = 𝟚} C↓ f (fst (snd (opfib tt x)))) tt)                        
            h-aux f =
              let x→Fx : Arrow↓ x (F x) tt
                  x→Fx = fst (snd (opfib tt x))

                  Gy→y : Arrow↓ (G y) y tt
                  Gy→y = fst (snd (fib tt y))

                  cart : is-cartesian X↓ Gy→y
                  cart = snd (snd (fib tt y))

                  h : Arrow↓ x y tt
                  h = comp↓ {C = 𝟚} C↓ f x→Fx 

              in cart false x tt h tt tt

            h : Arrow↓ (F x) y tt → Arrow↓ x (G y) tt
            h = fst ∘ contr-center ∘ h-aux

            g-h : g ∘ h ∼ idf _
            g-h f =
              let x→Fx : Arrow↓ x (F x) tt
                  x→Fx = fst (snd (opfib tt x))

                  Gy→y : Arrow↓ (G y) y tt
                  Gy→y = fst (snd (fib tt y))

                  cart : is-cartesian {!!} Gy→y
                  cart = snd (snd (fib tt y))

                  cocart : is-cocartesian {!!} x→Fx
                  cocart = snd (snd (opfib tt x))

                  k : Arrow↓ x y tt
                  k = comp↓ {C = 𝟚} C↓ f x→Fx

                  foo1 : _==_ {A = Σ (Arrow↓ x y tt) λ f' → Simplex↓ (fst (contr-center (h-aux f))) Gy→y f' tt}
                             (comp↓ {C = 𝟚} C↓ Gy→y (h f) , fill↓ {C = 𝟚} C↓ Gy→y (fst (contr-center (h-aux f))))
                             (comp↓ {C = 𝟚} C↓ f x→Fx , snd (contr-center (h-aux f)))
                  foo1 = contr-has-all-paths ⦃{! base-fibrant↓ fib↓ ? _ _ (pd-cells↓ X↓ Gy→y (h f)) ? !} ⦄ _ _

                  foo2 : Σ (Arrow↓ (F x) y tt) λ k' →
                          Simplex↓ x→Fx k' k tt
                  foo2 = g (h f) , transport (λ z → Simplex↓ x→Fx (g (h f)) z tt)
                                             (fst= foo1)
                                             (snd (contr-center (g-aux (h f))))

                  

              in fst= $ contr-has-all-paths ⦃ cocart true y tt k tt tt ⦄ {!!} (f , {! fill↓ (𝟚 , C↓ , C↓-is-1-category) f x→Fx!})

            h-g : h ∘ g ∼ idf _
            h-g = {!!}
