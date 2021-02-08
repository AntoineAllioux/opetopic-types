{-# OPTIONS --rewriting --without-K #-}

open import CategoryTheory.InftyCategories
open import CategoryTheory.Interval
open import CategoryTheory.Fibrations
open import OpetopicType
open import IdentityMonad
open import HoTT

module CategoryTheory.Functors where

  module _ {C : ∞-category} (C↓ : ∞-category↓ C) where

    private
      X = fst C
      fib = snd C
      X↓ = fst C↓
      fib↓ = snd C↓

    comp↓ : {x y z : Obj X} {x↓ : Obj↓ X↓ x} {y↓ : Obj↓ X↓ y} {z↓ : Obj↓ X↓ z}
      → {g : Arrow X y z} {f : Arrow X x y}
      → (g↓ : Arrow↓ X↓ y↓ z↓ g) (f↓ : Arrow↓ X↓ x↓ y↓ f) 
      → Arrow↓ X↓ x↓ z↓ (compₒ C g f)
    comp↓ {g = g} {f = f} g↓ f↓ = fst (contr-center (base-fibrant↓ fib↓ {!!} {!!} {!!} (compₒ C g f) (fillₒ C g f)))

    fill↓ : {x y z : Obj X} {x↓ : Obj↓ X↓ x} {y↓ : Obj↓ X↓ y} {z↓ : Obj↓ X↓ z}
      → {g : Arrow X y z} {f : Arrow X x y}
      → (g↓ : Arrow↓ X↓ y↓ z↓ g) (f↓ : Arrow↓ X↓ x↓ y↓ f) 
      → Simplex↓ X↓ f↓ g↓ (comp↓ g↓ f↓) (fillₒ C g f)
    fill↓ {g = g} {f = f} g↓ f↓ = snd (contr-center (base-fibrant↓ fib↓ {!!} {!!} {!!} (compₒ C g f) (fillₒ C g f)))

  module _ (C↓ : ∞-category↓ 𝟚)
           (fib : is-fibration (fst C↓))
           (opfib : is-opfibration (fst C↓)) where
    
    private
      X↓ = fst C↓
      fib↓ = snd C↓

    F : Ob↓ X↓ ttᵢ tt false → Ob↓ X↓ ttᵢ tt true
    F x = fst (opfib tt x)

    G : Ob↓ X↓ ttᵢ tt true → Ob↓ X↓ ttᵢ tt false
    G x = fst (fib tt x)

    adj : (x : Ob↓ X↓ ttᵢ tt false)
      → (y : Ob↓ X↓ ttᵢ tt true)
      → Arrow↓ X↓ x (G y) tt
        ≃ Arrow↓ X↓ (F x) y tt
    adj x y = g , is-eq g h g-h h-g
      where g-aux : (f : Arrow↓ X↓ x (G y) tt)
                  → is-contr (Σ (Arrow↓ X↓ (F x) y tt) λ p →
                                 Simplex↓ X↓ (fst (snd (opfib tt x))) p
                                          (comp↓ {C = 𝟚} C↓ (fst (snd (fib tt y))) f) tt)
            g-aux f =
              let x→Fx : Arrow↓ X↓ x (F x) tt
                  x→Fx = fst (snd (opfib tt x))

                  cocart : is-cocartesian X↓ x→Fx
                  cocart = snd (snd (opfib tt x))

                  Gy→y : Arrow↓ X↓ (G y) y tt
                  Gy→y = fst (snd (fib tt y))
 
                  h : Arrow↓ X↓ x y tt
                  h = comp↓ {C = 𝟚} C↓ Gy→y f 

              in cocart true y tt h tt tt

            g : Arrow↓ X↓ x (G y) tt → Arrow↓ X↓ (F x) y tt
            g = fst ∘ contr-center ∘ g-aux

            h-aux : (f : Arrow↓ X↓ (F x) y tt)
              → is-contr (Σ (Arrow↓ X↓ x (G y) tt) λ f' →
                            Simplex↓ X↓ f' (fst (snd (fib tt y)))
                                     (comp↓ {C = 𝟚} C↓ f (fst (snd (opfib tt x)))) tt)                        
            h-aux f =
              let x→Fx : Arrow↓ X↓ x (F x) tt
                  x→Fx = fst (snd (opfib tt x))

                  Gy→y : Arrow↓ X↓ (G y) y tt
                  Gy→y = fst (snd (fib tt y))

                  cart : is-cartesian X↓ Gy→y
                  cart = snd (snd (fib tt y))

                  h : Arrow↓ X↓ x y tt
                  h = comp↓ {C = 𝟚} C↓ f x→Fx 

              in cart false x tt h tt tt

            h : Arrow↓ X↓ (F x) y tt → Arrow↓ X↓ x (G y) tt
            h = fst ∘ contr-center ∘ h-aux

            g-h : g ∘ h ∼ idf _
            g-h f =
              let x→Fx : Arrow↓ X↓ x (F x) tt
                  x→Fx = fst (snd (opfib tt x))

                  Gy→y : Arrow↓ X↓ (G y) y tt
                  Gy→y = fst (snd (fib tt y))

                  cart : is-cartesian X↓ Gy→y
                  cart = snd (snd (fib tt y))

                  cocart : is-cocartesian X↓ x→Fx
                  cocart = snd (snd (opfib tt x))

                  k : Arrow↓ X↓ x y tt
                  k = comp↓ {C = 𝟚} C↓ f x→Fx

                  foo1 : _==_ {A = Σ (Arrow↓ X↓ x y tt) λ f' → Simplex↓ X↓ (fst (contr-center (h-aux f))) Gy→y f' tt}
                             (comp↓ {C = 𝟚} C↓ Gy→y (h f) , fill↓ {C = 𝟚} C↓ Gy→y (fst (contr-center (h-aux f))))
                             (comp↓ {C = 𝟚} C↓ f x→Fx , snd (contr-center (h-aux f)))
                  foo1 = contr-has-all-paths ⦃{! base-fibrant↓ fib↓ ? _ _ (pd-cells↓ X↓ Gy→y (h f)) ? !} ⦄ _ _

                  foo2 : Σ (Arrow↓ X↓ (F x) y tt) λ k' →
                          Simplex↓ X↓ x→Fx k' k tt
                  foo2 = g (h f) , transport (λ z → Simplex↓ X↓ x→Fx (g (h f)) z tt)
                                             (fst= foo1)
                                             (snd (contr-center (g-aux (h f))))

                  

              in fst= $ contr-has-all-paths ⦃ cocart true y tt k tt tt ⦄ {!!} (f , {! fill↓ (𝟚 , C↓ , C↓-is-1-category) f x→Fx!})

            h-g : h ∘ g ∼ idf _
            h-g = {!!}
