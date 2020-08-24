{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import Monad
open import MonadOver
open import MonadMap
open import HoTT
open import Utils
open import OpetopicType

module MonadMapOver where


  record _⇛_[_] {M N : 𝕄} (M↓ : 𝕄↓ M) (N↓ : 𝕄↓ N) (f : M ⇛ N) : Set where
    field
      idx-map↓ : {i : Idx M} → Idx↓ M↓ i → Idx↓ N↓ (idx-map f i)
      cns-map↓ : {i : Idx M} {c : Cns M i} {i↓ : Idx↓ M↓ i}
        → Cns↓ M↓ i↓ c → Cns↓ N↓ (idx-map↓ i↓) (cns-map f c)
      typ-map↓ : {i : Idx M} {i↓ : Idx↓ M↓ i} {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c) (p : Pos M c)
        → idx-map↓ (Typ↓ M↓ c↓ p) == Typ↓ N↓ (cns-map↓ c↓) (–> (pos-map f c) p) [ Idx↓ N↓ ↓ typ-map f c p ]
      cns-map-η↓ : {i : Idx M} (i↓ : Idx↓ M↓ i)
        → cns-map↓ (η↓ M↓ i↓) == η↓ N↓ (idx-map↓ i↓) [ (Cns↓ N↓ (idx-map↓ i↓)) ↓ cns-map-η f i ]
      cns-map-μ↓ : {i : Idx M} {i↓ : Idx↓ M↓ i} {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
        → {δ : (p : Pos M c) → Cns M (Typ M c p)}
        → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
        → cns-map↓ (μ↓ M↓ c↓ δ↓)
          == μ↓ N↓ (cns-map↓ c↓) (λ p →
             let c↓₂ = cns-map↓ $ δ↓ (<– (pos-map f c) p)
                
               
                 i= : idx-map f (Typ M c (<– (pos-map f c) p)) == Typ N (cns-map f c) p
                 i= = typ-map f c (<– (pos-map f c) p)
                      ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p)

                 i↓ : idx-map↓ (Typ↓ M↓ c↓ (<– (pos-map f c) p)) == Typ↓ N↓ (cns-map↓ c↓) p
                      [ Idx↓ N↓ ↓ typ-map f c (<– (pos-map f c) p)
                                  ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p)  ]
                 i↓ = typ-map↓ c↓ (<– (pos-map f c) p)
                      ∙ᵈ ↓-ap-in _ (Typ N (cns-map f c))
                                   (apd (Typ↓ N↓ (cns-map↓ c↓)) (<–-inv-r (pos-map f c) p))


                 c= : cns-map f (δ (<– (pos-map f c) p))
                      == transport (Cns N) i= (cns-map f (δ (<– (pos-map f c) p))) [ Cns N ↓ i= ]
                 c= = transp-↓' _ i= (cns-map f (δ (<– (pos-map f c) p)))
                

              in transport (λ { (_ , i↓ , c) → Cns↓ N↓ i↓ c }) (pair= i= (↓-×-in i↓ c=)) c↓₂)
            [ (λ c↓ → Cns↓ N↓ (idx-map↓ i↓) c↓) ↓ cns-map-μ f c δ ]
            
  open _⇛_[_] public

  idmap↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → M↓ ⇛ M↓ [ idmap M ]
  idx-map↓ (idmap↓ M↓) = idf _
  cns-map↓ (idmap↓ M↓) = idf _
  typ-map↓ (idmap↓ M↓) _ _ = idp
  cns-map-η↓ (idmap↓ M↓) _ = idp
  cns-map-μ↓ (idmap↓ M↓) _ _ = idp
  

  module _ {M : 𝕄} {M↓ : 𝕄↓ M} {N : 𝕄} {N↓ : 𝕄↓ N}
    {f : M ⇛ N} (f↓ : M↓ ⇛ N↓ [ f ])
    {A : Idx M → Set}
    {A↓ : (i : Idx M) → Idx↓ M↓ i → A i → Set}
    {B : Idx N → Set}
    {B↓ : (i : Idx N) → Idx↓ N↓ i → B i → Set} where

    Pb-map↓ : {g : {i : Idx M} → A i → B (idx-map f i)}
      → (g↓ : {i : Idx M} {i↓ : Idx↓ M↓ i} {x : A i}
        → A↓ i i↓ x → B↓ (idx-map f i) (idx-map↓ f↓ i↓) (g x))
      → Pb↓ M↓ A A↓ ⇛ Pb↓ N↓ B B↓ [ Pb-map' f g ]
    idx-map↓ (Pb-map↓ g↓) (i , x) = idx-map↓ f↓ i , g↓ x
    cns-map↓ (Pb-map↓ {g} g↓) {c = c , ν} (c↓ , ν↓) =
      let ν' p =
             let x↓ : B↓ (idx-map f (Typ M c (<– (pos-map f c) p)))
                          (idx-map↓ f↓ (Typ↓ M↓ c↓ (<– (pos-map f c) p)))
                          (g (ν (<– (pos-map f c) p)))
                 x↓ = g↓ (ν↓ (<– (pos-map f c) p))

                 i= : idx-map f (Typ M c (is-equiv.g (snd (pos-map f c)) p))
                      == Typ N (cns-map f c) p
                 i= = typ-map f c (<– (pos-map f c) p)
                      ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p)

                 i↓= : idx-map↓ f↓ (Typ↓ M↓ c↓ (<– (pos-map f c) p))
                       == Typ↓ N↓ (cns-map↓ f↓ c↓) p [ Idx↓ N↓ ↓ i=  ]
                 i↓= = typ-map↓ f↓ c↓ (<– (pos-map f c) p)
                   ∙ᵈ ↓-ap-in _ (Typ N (cns-map f c))
                                (apd (Typ↓ N↓ (cns-map↓ f↓ c↓)) (<–-inv-r (pos-map f c) p))
                 
             in transport (λ {(i , (c , x)) → B↓ i c x })
                          (pair= i= (↓-×-in i↓= (transp-↓' _ i= (g (ν (<– (pos-map f c) p))))))
                          x↓
      in cns-map↓ f↓ c↓ , {!!}
    typ-map↓ (Pb-map↓ g↓) = {!!}
    cns-map-η↓ (Pb-map↓ g↓) = {!!}
    cns-map-μ↓ (Pb-map↓ g↓) = {!!}



  module _ {M : 𝕄} {M↓ : 𝕄↓ M} {N : 𝕄} {N↓ : 𝕄↓ N}
    {f : M ⇛ N} (f↓ : M↓ ⇛ N↓ [ f ]) where


    cns-map↓ₛ : {i : Idxₛ M} {i↓ : Idx↓ₛ M↓ i} {c : Cnsₛ M i}
      → Cns↓ₛ M↓ i↓ c
      → Cns↓ₛ N↓ (idx-map↓ f↓ (fst i↓) , cns-map↓ f↓ (snd i↓)) (cns-mapₛ f c)
    cns-map↓ₛ (lf↓ {i} i↓) = lf↓ (idx-map↓ f↓ i↓)
      |> transport (λ { (_ , x , y) → Pd↓ N↓ (idx-map↓ f↓ i↓ , x) y })
                   (pair=
                     (! (cns-map-η f i))
                     (↓-×-in
                       (!ᵈ (cns-map-η↓ f↓ i↓))
                       (transp-↓' _ (! (cns-map-η f i)) (lf (idx-map f i)))))
                            
    cns-map↓ₛ {c = nd c δ ε} (nd↓ {i↓ = i↓} c↓ δ↓ ε↓) =
      let i= : (p : Pos N (cns-map f c)) → idx-map f (Typ M c (is-equiv.g (snd (pos-map f c)) p))
               == Typ N (cns-map f c) p
          i= p = typ-map f c (<– (pos-map f c) p)
                 ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p)

          i↓= : (p : Pos N (cns-map f c)) → idx-map↓ f↓ (Typ↓ M↓ c↓ (<– (pos-map f c) p))
                == Typ↓ N↓ (cns-map↓ f↓ c↓) p [ Idx↓ N↓ ↓ i= p  ]
          i↓= p = typ-map↓ f↓ c↓ (<– (pos-map f c) p)
                  ∙ᵈ ↓-ap-in _ (Typ N (cns-map f c))
                               (apd (Typ↓ N↓ (cns-map↓ f↓ c↓)) (<–-inv-r (pos-map f c) p))

          δ↓₁ p = cns-map↓ f↓ (δ↓ (<– (pos-map f c) p))
                  |> transport (λ { (_ , i↓ , c)  → Cns↓ N↓ i↓ c })
                       (pair=
                         (i= p)
                         (↓-×-in
                           (i↓= p)
                           (transp-↓' _ (i= p) (cns-map f (δ (<– (pos-map f c) p))))))
          ε↓₁ p =
            let lem : {A : Set} {B C : A → Set}
                      → {D : Σ A (λ x → B x × C x) → Set}
                      → {x x₁ : A} {y : B x} {y₁ : B x₁}
                      → {z : C x} {z₁ : C x₁}
                      → {t : D (x , y , z)} {t₁ : D (x₁ , y₁ , z₁)}
                      → (p : x == x₁) (q : y == y₁ [ B ↓ p ])
                      → (r : z == z₁ [ C ↓ p ]) (s : t == t₁ [ D ↓ pair= p (↓-×-in q r) ])
                      → ap (λ { ((i , i↓ , c) , c↓) → (i , c) }) (pair= (pair= p (↓-×-in q r)) s) == pair= p r
                lem = λ { idp idp idp idp → idp }

                pth = transp-↓' _ (pair= (i= p) (transp-↓' _ (i= p) (cns-map f (δ (<– (pos-map f c) p)))))
                                  (cns-mapₛ f (ε (<– (pos-map f c) p)))  

            in cns-map↓ₛ (ε↓ (<– (pos-map f c) p))
                  |> transport (λ { (((i , i↓ , c) , c↓) , pd) → Pd↓ N↓ (i↓ , c↓) pd })
                       (pair= 
                         (pair=
                           (pair=
                             (i= p)
                             (↓-×-in
                               (i↓= p)
                               (transp-↓' _ (i= p) (cns-map f (δ (<– (pos-map f c) p))))))
                           (transp-↓' _ _ (cns-map↓ f↓ $ δ↓ (<– (pos-map f c) p))))
                         (↓-ap-out (Pd N) (λ { ((i , i↓ , c) , c↓) → (i , c) }) _
                                   (transport (λ x → _ == _ [ _ ↓ x ]) (! (lem (i= p) (i↓= p) _ _)) pth)))

      in nd↓ (cns-map↓ f↓ c↓) δ↓₁ ε↓₁
         |> transport↓ (λ { (x , y) → Pd↓ N↓ (idx-map↓ f↓ i↓ , x) y })
                       (! (cns-map-μ f c δ))
                       (↓-×-in (!ᵈ (cns-map-μ↓ f↓ c↓ δ↓)) (transp-↓' _ (! (cns-map-μ f c δ)) _))

    Slice-map↓ : Slice↓ M↓ ⇛ Slice↓ N↓ [ Slice-map f ]
    idx-map↓ Slice-map↓ (i↓ , c↓) = idx-map↓ f↓ i↓ , cns-map↓ f↓ c↓
    cns-map↓ Slice-map↓ = cns-map↓ₛ
    typ-map↓ Slice-map↓ = {!!}
    cns-map-η↓ Slice-map↓ = {!!}
    cns-map-μ↓ Slice-map↓ = {!!}


  {-# TERMINATING #-}
  OpType-map↓ : {M : 𝕄} {M↓ : 𝕄↓ M}
    → {N : 𝕄} {N↓ : 𝕄↓ N}
    → {f : M ⇛ N} (f↓ : M↓ ⇛ N↓ [ f ])
    → {X : OpetopicType N} (X↓ : OpetopicTypeOver N↓ X)
    → OpetopicTypeOver M↓ (OpType-map f X)
  Ob↓ (OpType-map↓ {f = f} f↓ X↓) i i↓ x = Ob↓ X↓ (idx-map f i) (idx-map↓ f↓ i↓) x
  Hom↓ (OpType-map↓ f↓ X↓) = OpType-map↓ (Slice-map↓ (Pb-map↓ f↓ (idf _))) (Hom↓ X↓)
