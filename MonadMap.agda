{-# OPTIONS --without-K --rewriting --allow-unsolved-meta #-}

open import Monad
open import Pb
open import OpetopicType
open import HoTT

module MonadMap where

  _⇒_ : {A : Set} (B C : A → Set) → Set
  _⇒_ {A} B C = (x : A) → B x → C x

  transp!-∙ : ∀ {i j} {A : Type i} {B : A → Type j} {x y z : A}
    (p : x == y) (q : z == y) (b : B x)
    → transport B (p ∙ ! q) b == transport! B q (transport B p b)
  transp!-∙ idp idp b = idp

  C-transp : {A : Set} {B : A → Set} (C : {x : A} → B x → Set)
      → {x y : A} (p : x == y)
      → (u : B y)
      → C (transport! B p u) == C u
  C-transp C idp u = idp

  transp-↓' : ∀ {i j} {A : Type i} (P : A → Type j) {a₁ a₂ : A}
    → (p : a₁ == a₂) (y : P a₁) → y == transport P p y [ P ↓ p ]
  transp-↓' _ idp _ = idp

  record _⇛_ (M N : 𝕄) : Set where
    field
      idx-map : Idx M → Idx N
      cns-map : {i : Idx M} → Cns M i → Cns N (idx-map i)
      pos-map : {i : Idx M} (c : Cns M i)
        → Pos M c ≃ Pos N (cns-map c)
      typ-map : {i : Idx M} (c : Cns M i) (p : Pos M c)
        → idx-map (Typ M c p) == Typ N (cns-map c) (–> (pos-map c) p)
      cns-map-η : (i : Idx M) → cns-map (η M i) == η N (idx-map i)
      cns-map-μ : {i : Idx M} (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → cns-map (μ M c δ)
          == μ N (cns-map c) (λ p →
            transport (Cns N)
              (typ-map _ (<– (pos-map c) p)
               ∙ ap (Typ N (cns-map c)) (<–-inv-r (pos-map c) p))
              (cns-map (δ (<– (pos-map _) p))))
  open _⇛_

  idmap : (M : 𝕄) → M ⇛ M
  idx-map (idmap M) = idf _
  cns-map (idmap M) = idf _
  pos-map (idmap M) _ = ide _
  typ-map (idmap M) c p = idp
  cns-map-η (idmap M) i = idp
  cns-map-μ (idmap M) c δ = idp

  _∘ₘ_ : {A B C : 𝕄} (g : B ⇛ C) (f : A ⇛ B) → A ⇛ C
  idx-map (g ∘ₘ f) = idx-map g ∘ idx-map f
  cns-map (g ∘ₘ f) = cns-map g ∘ cns-map f
  pos-map (g ∘ₘ f) c = pos-map g (cns-map f c) ∘e pos-map f c
  typ-map (g ∘ₘ f) c p = ap (idx-map g) (typ-map f c p) ∙ typ-map g (cns-map f c) (–> (pos-map f c) p)
  cns-map-η (g ∘ₘ f) i = ap (cns-map g) (cns-map-η f i) ∙ cns-map-η g (idx-map f i)
  cns-map-μ (g ∘ₘ f) c δ = ap (cns-map g) (cns-map-μ f c δ) ∙ {!cns-map-μ g (cns-map f c) ?!}  

  Pb-map : {M : 𝕄} {A B : Idx M → Set}
    → (f : A ⇒ B)
    → Pb M A ⇛ Pb M B
  idx-map (Pb-map f) (i , x) = i , f i x
  cns-map (Pb-map f) (c , ν) = c , λ p → f _ (ν p)
  pos-map (Pb-map {M} f) (c , ν) = ide (Pos M c)
  typ-map (Pb-map f) c p = idp
  cns-map-η (Pb-map f) i = idp
  cns-map-μ (Pb-map f) c δ = idp

  module _ {M N : 𝕄} (f : M ⇛ N) where

    Pb-map' : (A : Idx M → Set) (B : Idx N → Set)
      → (g : {i : Idx M} → A i → B (idx-map f i))
      → Pb M A ⇛ Pb N B
    idx-map (Pb-map' A B g) (i , x) = idx-map f i , g x
    cns-map (Pb-map' A B g) (c , ν) =
      let ν' p = transport B
                 (typ-map f c (<– (pos-map f c) p) ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p))
                 (g (ν (<– (pos-map f _) p)))
      in cns-map f c , ν'
    pos-map (Pb-map' A B g) (c , _) = pos-map f c
    typ-map (Pb-map' A B g) (c , c₁) p = pair= (typ-map f c p) q
      where q : g (c₁ p)
                   == transport B {x = idx-map f (Typ M c (<– (pos-map f c) (–> (pos-map f c) p)) )} {y = Typ N (cns-map f c) (–> (pos-map f c) p)}
                                (typ-map f c (<– (pos-map f c) (–> (pos-map f c) p)) ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) (–> (pos-map f c) p)))
                      (g (c₁ (<– (pos-map f c) (–> (pos-map f c) p))))
                 [ B ↓ typ-map f c p ]
            q = from-transp! B (typ-map f c p)
                                (transport (λ x → _ == x) (transp!-∙ (typ-map f c (<– (pos-map f c) (–> (pos-map f c) p)) ∙
                                ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) (–> (pos-map f c) p))) (typ-map f c p) (g (c₁ (<– (pos-map f c) (–> (pos-map f c) p))))) {!!})            
    cns-map-η (Pb-map' A B g) (i , x) = pair= (cns-map-η f i) {!!}
    cns-map-μ (Pb-map' A B g) (c , c₁) δ = pair= {!!} {!!}

    cns-mapₛ : {i : Idxₛ M} → Cnsₛ M i → Cnsₛ N (idx-map f (fst i) , cns-map f (snd i))
    cns-mapₛ (lf i) = transport! (λ x → Cnsₛ N (idx-map f i , x)) (cns-map-η f i) (lf (idx-map f i))
    cns-mapₛ {.(_ , μ M c δ)} (nd c δ ε) =
            let hyp p = cns-mapₛ (ε p)
            in transport! (λ x → Cnsₛ N (idx-map f _ , x))
                          (cns-map-μ f c δ)
                          (nd (cns-map f c)
                              (λ p → transport (Cns N)
                                ((typ-map f c (<– (pos-map f _) p) ∙
                                  ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p)))
                                (cns-map f (δ (<– (pos-map f c) p ))))
                               λ p → transport (Pd N)
                                 (pair= (typ-map f c _ ∙
                                   ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p))
                                        (transp-↓' _ _ _))
                                 (hyp (<– (pos-map f c) p)))

    pos-mapₛ : {i : Idxₛ M} (c : Cnsₛ M i) → Posₛ M c ≃ Posₛ N (cns-mapₛ c)
    pos-mapₛ {i} c = g c , is-eq (g c) {!!} {!!} {!!}
      where g : {i : Idxₛ M} (c : Cnsₛ M i) → Posₛ M c → Posₛ N (cns-mapₛ c)
            g (lf i) ()
            g {i , _} (nd c δ ε) (inl x) =  coe! (C-transp {B = (λ x₁ → Cnsₛ N (idx-map f i , x₁))} (Posₛ N) (cns-map-μ f c δ) _) (inl x)
            g {i , _} (nd c δ ε) (inr (p , q)) =
              let hyp = g _ q
              in coe! (C-transp {B = (λ x₁ → Cnsₛ N (idx-map f i , x₁))} (Posₛ N) (cns-map-μ f c δ) _) (inr (–> (pos-map f c) p , {!!}))
          
    Slice-map : Slice M ⇛ Slice N
    idx-map Slice-map (i , c) = idx-map f i , cns-map f c
    cns-map Slice-map = cns-mapₛ
    pos-map Slice-map = pos-mapₛ
    typ-map Slice-map c p = pair= {!typ-map f ? ?!} {!!}
    cns-map-η Slice-map = {!!}
    cns-map-μ Slice-map = {!!}
    
  -- OpetopicType is contrafunctorial
  {-# TERMINATING #-}
  OpType-map : {M N : 𝕄}
    → (f : M ⇛ N)
    → OpetopicType N
    → OpetopicType M
  Ob (OpType-map f X) x = Ob X (idx-map f x)
  Hom (OpType-map f X) = OpType-map (Slice-map (Pb-map' f _ _ (idf _))) (Hom X)


  Op= : {M : 𝕄}
    → {A B : Idx M → Set}
    → {X : OpetopicType (Slice (Pb M A))}
    → {Y : OpetopicType (Slice (Pb M B))}
    → (Ob= : A == B)
    → (Hom= : X == Y [ (λ X → OpetopicType (Slice (Pb M X))) ↓ Ob= ])
    → record { Ob = A ; Hom = X } == record { Ob = B ; Hom = Y }
  Op= idp idp = idp

  OpType-unit : {M : 𝕄}
    → OpType-map (idmap M) ∼ idf (OpetopicType M)
  OpType-unit {M} x = {! Op= idp idp !}

  OpType-comp : {A B C : 𝕄}
    → (g : B ⇛ C) (f : A ⇛ B)
    → OpType-map (g ∘ₘ f) ∼ OpType-map f ∘ OpType-map g
  OpType-comp = {!!}
