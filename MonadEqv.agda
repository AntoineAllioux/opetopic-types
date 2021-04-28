{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import HoTT
open import Monad
open import Pb
open import OpetopicType

module MonadEqv where

  _≃[_]_ : {A B : Set} (P : A → Set) (e : A ≃ B) (Q : B → Set) → Set
  P ≃[ e ] Q  = (a : _) → P a ≃ Q (fst e a)  

  -- Super annoying this is large, but its because
  -- of the η-pos-elim, which quantifies over a family...
  record _≃ₘ_ (M N : 𝕄) : Set₁ where
    field

      Idx≃ : Idx M ≃ Idx N
      Cns≃ : (i : Idx M) → Cns M i ≃ Cns N (–> Idx≃ i) 
      Pos≃ : (i : Idx M) (c : Cns M i)
        → Pos M c ≃ Pos N (–> (Cns≃ i) c)

      -- Should we do this the other way and derive what we need below?
      Typ≃ : (i : Idx M) (c : Cns M i) (p : Pos N (–> (Cns≃ i) c))
        → –> Idx≃ (Typ M c (<– (Pos≃ i c) p)) == Typ N (–> (Cns≃ i) c) p

      η≃ : (i : Idx M)
        → –> (Cns≃ i) (η M i) == η N (–> Idx≃ i) 

      η-pos≃ : (i : Idx M)
        → –> (Pos≃ i (η M i)) (η-pos M i) == transport (Pos N) (! (η≃ i)) (η-pos N (–> Idx≃ i))

      -- Yikes.  We're going to need some helpers ...
      -- η-pos-elim≃ : (i : Idx M)
      --   → (X : (p : Pos M (η M i)) → Set)
      --   → (η-pos* : X (η-pos M i))
      --   → (p : Pos M (η M i))
      --   → η-pos-elim M i X η-pos* p ==
      --       transport X {!!} (η-pos-elim N (–> Idx≃ i) (λ pn → X (<– (Pos≃ i (η M i)) (transport (Pos N) (! (η≃ i)) pn)))
      --                                                  (transport (X ∘ <– (Pos≃ i (η M i))) (η-pos≃ i)
      --                                                             (transport! X (<–-inv-l (Pos≃ i (η M i)) (η-pos M i)) η-pos*))
      --                                                             (transport (Pos N) (η≃ i) (–> (Pos≃ i (η M i)) p)))

      μ≃ : (i : Idx M) (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → –> (Cns≃ i) (μ M c δ) == μ N (–> (Cns≃ i) c)
          (λ p → transport (Cns N) (Typ≃ i c p) (–> (Cns≃ (Typ M c (<– (Pos≃ i c) p))) (δ (<– (Pos≃ i c) p))))

  open _≃ₘ_ public

  id≃ₘ : (M : 𝕄) → M ≃ₘ M
  Idx≃ (id≃ₘ M) = ide _
  Cns≃ (id≃ₘ M) _ = ide _
  Pos≃ (id≃ₘ M) i c = ide _
  Typ≃ (id≃ₘ M) i c p = idp
  η≃ (id≃ₘ M) i = idp
  η-pos≃ (id≃ₘ M) i = idp
  μ≃ (id≃ₘ M) i c δ = idp

  -- These are the main things that we will need ...

  Pb≃ : {M N : 𝕄} (e : M ≃ₘ N)
    → {X : Idx M → Set}
    → {Y : Idx N → Set}
    → X ≃[ Idx≃ e ] Y
    → Pb M X ≃ₘ Pb N Y
  Idx≃ (Pb≃ e {X} {Y} f) = Σ-emap-l Y (Idx≃ e) ∘e Σ-emap-r f
  Cns≃ (Pb≃ {M} {N} e {X} {Y} f) (i , x) = Σ-emap-l {!!} (Cns≃ e i) ∘e Σ-emap-r λ c → {!? ∘e Π-emap-l ((λ c₁ → (p : Pos N c₁) → Y (Typ N c₁ p))) (Cns≃ e i) !} ⁻¹
  Pos≃ (Pb≃ e f) = {!!}
  Typ≃ (Pb≃ e f) = {!!}
  η≃ (Pb≃ e f) = {!!}
  η-pos≃ (Pb≃ e f) = {!!}
  μ≃ (Pb≃ e f) = {!!}

  Slice≃ : {M N : 𝕄}
    → M ≃ₘ N
    → Slice M ≃ₘ Slice N
  Idx≃ (Slice≃ {M} {N} e) = Σ-emap-l (Cns N) (Idx≃ e) ∘e Σ-emap-r (Cns≃ e)
  Cns≃ (Slice≃ e) i = {!!}
  Pos≃ (Slice≃ e) = {!!}
  Typ≃ (Slice≃ e) = {!!}
  η≃ (Slice≃ e) = {!!}
  η-pos≃ (Slice≃ e) = {!!}
  μ≃ (Slice≃ e) = {!!}


    Pb≃' : {M : 𝕄} 
      → {X : Idx M → Set}
      → {Y : Idx M → Set}
      → (ϕ : (i : Idx M) → X i ≃ Y i)
      → Pb M X ≃ₘ Pb M Y 

  op-transp : {M N : 𝕄} (eqv : M ≃ₘ N)
    → OpetopicType N → OpetopicType M
  Ob (op-transp eqv X) = Ob X ∘ –> (Idx≃ eqv)
  Hom (op-transp {M} {N} eqv X) = op-transp spb-eqv (Hom X)

    where spb-eqv : Slice (Pb M (Ob X ∘ –> (Idx≃ eqv))) ≃ₘ Slice (Pb N (Ob X))
          spb-eqv = Slice≃ (Pb≃ eqv (λ i → ide (Ob X (fst (Idx≃ eqv) i)))) 

  postulate

    op-transp-fib : {M N : 𝕄} (eqv : M ≃ₘ N)
      → (X : OpetopicType N) (is-fib : is-fibrant X)
      → is-fibrant (op-transp eqv X) 

  -- Equivalences of opetopic types
  record _≃ₒ_ {M : 𝕄} (X : OpetopicType M) (Y : OpetopicType M) : Set where
    coinductive
    field

      Ob≃ : (i : Idx M) → Ob X i ≃ Ob Y i
      Hom≃ : Hom X ≃ₒ op-transp (Slice≃ (Pb≃' Ob≃)) (Hom Y) 

  open _≃ₒ_ public
