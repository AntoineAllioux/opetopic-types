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
  Cns≃ (Pb≃ {M} {N} e {X} {Y} f) (i , x) =
    let pth : (c : Cns M i) (p : Pos M c)
               → Typ N (–> (Cns≃ e i) c) (–> (Pos≃ e i c) p) == –> (Idx≃ e) (Typ M c p)
        pth c p = ! (Typ≃ e _ _ _) ∙ ap (λ p → –> (Idx≃ e) (Typ M c p)) (<–-inv-l (Pos≃ e i c) p)

        eq : (c : Cns M i)
               → Π (Pos M c) (λ p → Y (–> (Idx≃ e) (Typ M c p)))
                 ≃ Π (Pos N (–> (Cns≃ e i) c)) λ p → Y (Typ N (–> (Cns≃ e i) c) p)
        eq c = transport (λ x → Π (Pos M c) (λ p → Y (x p)) ≃ Π (Pos N (–> (Cns≃ e i) c)) λ p → Y (Typ N _ p))
                         (λ= (pth c))
                         (Π-emap-l (λ p → Y (Typ N (–> (Cns≃ e i) c) p)) (Pos≃ e i c)) 
    in Σ-emap-l (λ c → (p : Pos N c) → Y (Typ N c p)) (Cns≃ e i)
       ∘e Σ-emap-r λ c → eq c ∘e  Π-emap-r λ p → f (Typ M c p)
  Pos≃ (Pb≃ e f) = {!!}
  Typ≃ (Pb≃ e f) = {!!}
  η≃ (Pb≃ e f) = {!!}
  η-pos≃ (Pb≃ e f) = {!!}
  μ≃ (Pb≃ e f) = {!!}

  Pb≃-id : (M : 𝕄) (X : Idx M → Set)
    → Pb≃ (id≃ₘ M) {X} {X} (λ i → ide (X i)) == id≃ₘ (Pb M X)
  Pb≃-id M X = {!!}
  
  transp-↓' : ∀ {i j} {A : Type i} (P : A → Type j) {a₁ a₂ : A}
    → (p : a₁ == a₂) (y : P a₁) → y == transport P p y [ P ↓ p ]
  transp-↓' _ idp _ = idp

  Slice≃ : {M N : 𝕄}
    → M ≃ₘ N
    → Slice M ≃ₘ Slice N
  Idx≃ (Slice≃ {M} {N} e) = Σ-emap-l (Cns N) (Idx≃ e) ∘e Σ-emap-r (Cns≃ e)
  Cns≃ (Slice≃ {M} {N} e) i = f , is-eq _ {!!} {!!} {!!}
    where f : {i : Idxₛ M} → Cnsₛ M i → Cnsₛ N (–> (Σ-emap-l (Cns N) (Idx≃ e) ∘e Σ-emap-r (Cns≃ e)) i)
          f (lf i) = transport (λ x → Cnsₛ N (–> (Idx≃ e) i , x)) (! (η≃ e i))  (lf (–> (Idx≃ e) i))
          f (nd {i} c δ ε) =
            let δ' : (p : Pos N (–> (Cns≃ e _) c)) → Cns N (Typ N (–> (Cns≃ e _) c) p)
                δ' p =
                  let σ =  –> (Cns≃ e _) (δ (<– (Pos≃ e _ c) p)) 
                  in transport (Cns N) (Typ≃ e _ c p) σ
                  
                ε' : (p : Pos N (–> (Cns≃ e _) c)) → Pd N (Typ N (–> (Cns≃ e _) c) p , δ' p)
                ε' p =
                  let pd = f (ε (<– (Pos≃ e _ c) p))
                  in transport (Pd N) (pair= (Typ≃ e _ c p) (transp-↓' (Cns N) (Typ≃ e _ c p) (–> (Cns≃ e (Typ M c (<– (Pos≃ e _ c) p))) (δ (<– (Pos≃ e _ c) p))))) pd
                     
            in transport (λ x → Pd N (–> (Idx≃ e) i , x))
                         (! (μ≃ e _ c δ))
                         (nd (–> (Cns≃ e _) c) δ' ε')
  Pos≃ (Slice≃ e) = {!!}
  Typ≃ (Slice≃ e) = {!!}
  η≃ (Slice≃ e) = {!!}
  η-pos≃ (Slice≃ e) = {!!}
  μ≃ (Slice≃ e) = {!!}

  Slice≃-id : (M : 𝕄)
    → Slice≃ (id≃ₘ M) == id≃ₘ (Slice M)
  Slice≃-id = {!!}

 

  Slice-Pb-id : (M : 𝕄) (X : Idx M → Set)
    → Slice≃ (Pb≃ (id≃ₘ M) λ i → ide (X i)) == id≃ₘ (Slice (Pb M X))
  Slice-Pb-id M X = {! ap (Slice≃ {Pb M X} {Pb M X}) ? !} ∙ Slice≃-id (Pb M X)

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
