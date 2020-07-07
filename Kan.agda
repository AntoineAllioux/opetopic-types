{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (lift)
open import Utils
open import Monad
open import OpetopicType
open import MonadOver
open import Pb
open import IdentityMonad

module Kan where
  
  module _ {M : 𝕄} (A : Idx M → Set) (W : Idx (Slice (Pb M A)) → Set) where

    has-comp : Set
    has-comp = (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → A (Typ M c p))
        → A i

    has-fill : has-comp → Set
    has-fill hc = (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → A (Typ M c p))
        → W ((i , hc i c ν) , c , ν)

    module _ (Z : Idx (Slice (Pb (Slice (Pb M A)) W)) → Set) where
    
      LiftCell : (τ : Idx M) (c : Cns M τ) (ν : (p : Pos M c) → A (Typ M c p))
        → (y z : A τ)
        → (p : W ((τ , y) , c , ν))
        → (q : W ((τ , z) , c , ν)) → Set
      LiftCell τ c ν y z p q = W ((τ , z) , η M τ , cst y)

      LiftFill : (τ : Idx M) (c : Cns M τ) (ν : (p : Pos M c) → A (Typ M c p))
        → (y z : A τ)
        → (p : W ((τ , y) , c , ν))
        → (q : W ((τ , z) , c , ν))
        → (ρ : LiftCell τ c ν y z p q)
        → Set
      LiftFill τ c ν y z p q ρ = 
         Z ((((τ , z) , c , ν) , q)
            , nd {i = τ , z} (η (Pb M A) (τ , y))
                             (η-pos-elim M τ _ (c , ν))
                             (η-pos-elim M τ _ (η (Slice (Pb M A)) ((τ , y) , c , ν)))
            , λ { true → ρ ;
                  (inr (s , t)) → η-pos-elim (Pb M A) (τ , y)
                    (λ s → (t : Posₛ (Pb M A) _) →
                       W (Typₛ (Pb M A) (η-pos-elim M τ (λ p₁ → Pd (Pb M A) _) (ηₛ (Pb M A) _) s) t) ) 
                    (η-pos-elim (Slice (Pb M A)) ((τ , y) , c , ν) (λ t → W (Typ (Slice (Pb M A)) _ t)) p)
                    s t })
                   
                                                      
      has-lift : Set
      has-lift = (τ : Idx M) (c : Cns M τ) (ν : (p : Pos M c) → A (Typ M c p))
        → (y z : A τ)
        → (p : W ((τ , y) , c , ν))
        → (q : W ((τ , z) , c , ν))
        → LiftCell τ c ν y z p q

      has-lift-fill : has-lift → Set
      has-lift-fill hd = (τ : Idx M) (c : Cns M τ) (ν : (p : Pos M c) → A (Typ M c p))
        → (y z : A τ)
        → (p : W ((τ , y) , c , ν))
        → (q : W ((τ , z) , c , ν))
        → LiftFill τ c ν y z p q (hd τ c ν y z p q)

      is-complete' : Set
      is-complete' = (τ : Idx M) (c : Cns M τ) (ν : (p : Pos M c) → A (Typ M c p))
        → (y z : A τ)
        → (p : W ((τ , y) , c , ν))
        → (q : W ((τ , z) , c , ν))
        → ((y , p) == (z , q)) ≃ Σ (LiftCell τ c ν y z p q) (LiftFill τ c ν y z p q)

  record is-kan {M : 𝕄} (X : OpetopicType M) : Set where
    coinductive
    field
      cmp : has-comp {M} (Ob X) (Ob (Hom X))
      fill : has-fill {M} (Ob X) (Ob (Hom X)) cmp
      lift : has-lift (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X)))
      lift-fill : has-lift-fill (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) lift
      hom-kan : is-kan (Hom X)
  open is-kan

  {-# ETA is-kan #-}
  
  is-kan= : {M : 𝕄} {X : OpetopicType M}
    {cmp cmp' : has-comp {M} (Ob X) (Ob (Hom X))}
    (cmp= : cmp == cmp')
    {fill : has-fill {M} (Ob X) (Ob (Hom X)) cmp}
    {fill' : has-fill {M} (Ob X) (Ob (Hom X)) cmp'}
    (fill= : fill == fill' [ has-fill {M} (Ob X) (Ob (Hom X)) ↓ cmp= ])
    {lift lift' : has-lift (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X)))}
    (lift= : lift == lift')
    {lift-fill : has-lift-fill (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) lift}
    {lift-fill' : has-lift-fill (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) lift'}
    (lift-fill= : lift-fill == lift-fill' [ _ ↓ lift= ])
    {hom-kan hom-kan' : is-kan (Hom X)}
    (hom-kan= : hom-kan == hom-kan')
    → _==_ {A = is-kan X}
      record { cmp = cmp ; fill = fill ; lift = lift ;
               lift-fill = lift-fill ; hom-kan = hom-kan }
      record { cmp = cmp' ; fill = fill' ; lift = lift' ;
               lift-fill = lift-fill' ; hom-kan = hom-kan' }
  is-kan= cmp= fill= lift= lift-fill= hom-kan= =
    ap (λ { (cmp , fill , lift , lift-fill , hom-kan) →
          record { cmp = cmp ; fill = fill ; lift = lift ;
                   lift-fill = lift-fill ; hom-kan = hom-kan } } )
       (pair= cmp= (↓-Σ-in fill= (↓-cst-in (pair= lift=
              (↓-Σ-in lift-fill= (↓-cst-in hom-kan=))))))

  record is-complete {M : 𝕄} (X : OpetopicType M) : Set where
    coinductive
    field
      base-complete : is-complete' (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X)))
      hom-complete : is-complete (Hom X)
      
  open is-complete

  is-complete= : {M : 𝕄} {X : OpetopicType M}
    → {base-complete base-complete' : is-complete' (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X)))}
    → (base-complete= : base-complete == base-complete')
    → {hom-complete hom-complete' : is-complete (Hom X)}
    → (hom-complete= : hom-complete == hom-complete')
    → _==_ {A = is-complete X}
       record { base-complete = base-complete ; hom-complete = hom-complete }
       record { base-complete = base-complete' ; hom-complete = hom-complete' }
  is-complete= base-complete= hom-complete= =
    ap (λ { (base-complete , hom-complete) →
          record { base-complete = base-complete ; hom-complete = hom-complete } })
       (pair×= base-complete= hom-complete=)

  module _ {M : 𝕄} {X : OpetopicType M} (cmpl : is-complete X) (k : is-kan X) where

    cellfrom-is-contr : (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Ob X (Typ M c p))
      → is-contr (Σ (Ob X i) (λ v → Ob (Hom X) ((i , v) , c , ν)))
    cellfrom-is-contr i c ν = has-level-in (ctr , pth)
            where ctr = cmp k i c ν , fill k i c ν

                  pth : (x : Σ (Ob X i) (λ v → Ob (Hom X) ((i , v) , c , ν)))
                    → ctr == x
                  pth (cmp , fill) = <– (base-complete cmpl i c ν _ _ _ _)
                    (lift k i c ν _ _ _ _ , lift-fill k i c ν _ _ _ _)

    lift-fill-is-contr : (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Ob X (Typ M c p))
      → (y z : Ob X i)
      → (p : Ob (Hom X) ((i , y) , c , ν))
      → (q : Ob (Hom X) ((i , z) , c , ν))
      → is-contr (Σ (LiftCell (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) i c ν y z p q)
                    (LiftFill (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) i c ν y z p q))  
    lift-fill-is-contr i c ν y z p q =
      equiv-preserves-level
        (base-complete cmpl i c ν y z p q)
        ⦃ =-preserves-level (cellfrom-is-contr i c ν) ⦄
                  

  {-# TERMINATING #-}
  is-kan-is-prop : {M : 𝕄} (X : OpetopicType M) → is-complete X → is-prop (is-kan X)
  is-kan-is-prop {M} X cmpl =
    all-paths-is-prop λ k k₁ →
      is-kan= (λ= λ i → λ= λ c → λ= λ ν →
                fst= (contr-has-all-paths ⦃ cellfrom-is-contr cmpl k i c ν ⦄ _ _))
              (λ=↓ _ (λ i → λ=↓ _ (λ c → λ=↓ _ (λ ν →
                snd= (contr-has-all-paths ⦃ cellfrom-is-contr cmpl k i c ν ⦄ _ _)))))
              (λ= λ i → λ= λ c → λ= λ ν → λ= λ y → λ= λ z → λ= λ p → λ= λ q →
                fst= (contr-has-all-paths ⦃ lift-fill-is-contr cmpl k i c ν y z p q ⦄ _ _))
              (λ=↓ _ (λ i → λ=↓ _ (λ c → λ=↓ _ (λ ν → λ=↓ _ (λ y → λ=↓ _ (λ z → λ=↓ _ (λ p → λ=↓ _  (λ q →
                snd= (contr-has-all-paths ⦃ lift-fill-is-contr cmpl k i c ν y z p q ⦄ _ _)))))))))
              (prop-has-all-paths ⦃ is-kan-is-prop (Hom X) (hom-complete cmpl) ⦄ _ _)

  {-# TERMINATING #-}
  lem : {M : 𝕄} (X : OpetopicType M) (ic : is-complete X) → is-kan X ≃ is-fibrant X
  lem {M} X cmpl = f , is-eq f g f-g g-f
    where f : is-kan X → is-fibrant X
          base-fibrant (f kan) i σ ν = cellfrom-is-contr cmpl kan i σ ν
          hom-fibrant (f kan) = –> (lem (Hom X) (hom-complete cmpl)) (hom-kan kan) 

          g : is-fibrant X → is-kan X
          cmp (g fib) i c ν = fst $ contr-center $ base-fibrant fib i c ν
          fill (g fib) i c ν = snd $ contr-center $ base-fibrant fib i c ν
          hom-kan (g fib) = <– (lem (Hom X) (hom-complete cmpl)) (hom-fibrant fib)
          lift (g fib) τ c ν y z p q = fst
            (–> (base-complete cmpl τ c ν y z p q)
                (contr-has-all-paths ⦃ base-fibrant fib τ c ν ⦄ (y , p) (z , q)))   
          lift-fill (g fib) τ c ν y z p q = snd
            (–> (base-complete cmpl τ c ν y z p q)
                (contr-has-all-paths ⦃ base-fibrant fib τ c ν ⦄ (y , p) (z , q)))

          f-g : f ∘ g ∼ idf _
          f-g x = prop-has-all-paths ⦃ is-fibrant-is-prop X ⦄ _ _

          g-f : g ∘ f ∼ idf _
          g-f k = prop-has-all-paths ⦃ is-kan-is-prop X cmpl ⦄ _ _
