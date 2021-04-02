{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import SigmaMonad
open import OpetopicType
open import MonadMap

module FreeAlg2 where

  postulate
    μ-pos-typ-slc : (M : 𝕄) {i : Idx (Slice M)} (c : Cns (Slice M) i)
      → (δ : (p : Pos (Slice M) c) → Cns (Slice M) (Typ (Slice M) c p))
      → (p : Pos (Slice M) (μ (Slice M) c δ))
      → Typₛ M (μ (Slice M) c δ) p ↦ Typ (Slice M) (δ (μ-pos-fst (Slice M) c δ p)) (μ-pos-snd (Slice M) c δ p)
    {-# REWRITE μ-pos-typ-slc #-}

  record is-fillable  {M : 𝕄} (X : OpetopicType M) : Set where
    coinductive
    field
      base-fillable : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Ob X (Typ M c p))
        → Σ (Ob X i) λ τ → Ob (Hom X) ((i , τ) , c , ν)
      hom-fillable : is-fillable (Hom X)

  open is-fillable

  Z : (M : 𝕄) (X : Idx M → Set) (Y : Idx (Slice (Pb M X)) → Set)
    → Idx (Slice (Pb M (⟦ M ⟧ X))) → Set
  Z M X Y ((i , x) , c , ν) =
    let f = idx-map (Slice-map (Pb-map' (idmap M) {B = ⟦ M ⟧ X} λ {i} x → η M i , cst x))
        c' = μ M c (fst ∘ ν)
        ν' p = η M (Typ M (μ M c (fst ∘ ν)) p) ,
               cst (snd (ν (μ-pos-fst M c (fst ∘ ν) p)) (μ-pos-snd M c (fst ∘ ν) p))
    in Σ (hfiber f ((i , x) , c' , ν')) (Y ∘ fst)
       ⊔ (μ M c (fst ∘ ν) , (λ p → snd (ν (μ-pos-fst M c (fst ∘ ν) p)) (μ-pos-snd M c (fst ∘ ν) p)) == x) 

  free-slice : (M : 𝕄) (X : Idx M → Set)
    → (Y : OpetopicType (Slice (Pb M X)))
    → OpetopicType (Slice (Pb M (⟦ M ⟧ X)))
  Ob (free-slice M X Y) = ⟦ Slice (Pb M (⟦ M ⟧ X)) ⟧ (Z M X (Ob Y))
  Hom (free-slice M X Y) =
    free-slice (Slice (Pb M (⟦ M ⟧ X)))
               (Z M X (Ob Y))
               (OpType-map* (Slice-map (Pb-map'
                              (Slice-map (Pb-map' (idmap M) (λ {i} x → η M i , cst x)))
                              (λ {i} x → inl ((_ , idp) , x))))
                            (Hom Y))
                            
  free : (M : 𝕄) (X : OpetopicType M) → OpetopicType M
  Ob (free M X) = ⟦ M ⟧ (Ob X)
  Hom (free M X) = free-slice _ _ (Hom X)

  free-slice-is-fillable : (M : 𝕄) (X : Idx M → Set)
    → (Y : OpetopicType (Slice (Pb M X)))
    → is-fillable (free-slice M X Y)
  base-fillable (free-slice-is-fillable M X Y) i c ν =
    let c' = μ (Slice (Pb M (⟦ M ⟧ X))) c (fst ∘ ν)
        ν' p = snd (ν (μ-pos-fst (Slice (Pb M (⟦ M ⟧ X))) c (fst ∘ ν) p))
                   (μ-pos-snd (Slice (Pb M (⟦ M ⟧ X))) c (fst ∘ ν) p)
        θ = η (Slice ((Pb (Slice (Pb M (⟦ M ⟧ X))) (⟦ Slice (Pb M (⟦ M ⟧ X)) ⟧ (Z M X (Ob Y)))))) _  ,
            λ { true → inr idp }
    in (c' , ν') , θ
     
  hom-fillable (free-slice-is-fillable M X Y) =
    let f = Slice-map (Pb-map'
              (Slice-map (Pb-map' (idmap M)
                                  (λ {i} x → η M i , cst x)))
              {B = Z M X (Ob Y)} (λ {i} x → inl ((_ , idp) , x)))
    in free-slice-is-fillable _ _ (OpType-map* {!f!} (Hom Y))

  free-is-fillable : (M : 𝕄) (X : OpetopicType M)
    → is-fillable (free M X)
  base-fillable (free-is-fillable M X) i c ν =
    let c' = μ M c (fst ∘ ν)
        ν' p = snd (ν (μ-pos-fst M c (fst ∘ ν) p)) (μ-pos-snd M c (fst ∘ ν) p)
        θ = η (Slice (Pb M (⟦ M ⟧ (Ob X)))) _ , λ { true → inr idp }
    in (c' , ν') , θ
  hom-fillable (free-is-fillable M X) = free-slice-is-fillable M (Ob X) (Hom X)
