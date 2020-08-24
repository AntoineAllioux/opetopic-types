{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import Monad
open import MonadOver
open import OpetopicType
open import Pb
open import IdentityMonad
open import IdentityMonadOver
open import SigmaMonad
open import Sigma
open import MonadMap
open import MonadMapOver
open import Utils

module Pi where

  -- We are going to start with the axiomatization of monadic terms
  postulate

    𝕋 : {M : 𝕄} (M↓ : 𝕄↓ M) → Set 

    idx : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
      → (i : Idx M) → Idx↓ M↓ i
      
    cns : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
      → {i : Idx M} (c : Cns M i)
      → Cns↓ M↓ (idx t i) c

    -- Term compatibility rewrites
    cns-typ : {M : 𝕄} {M↓ : 𝕄↓ M} 
      → (t : 𝕋 M↓) (i : Idx M)
      → (c : Cns M i) (p : Pos M c)
      → Typ↓ M↓ (cns t c) p ↦ idx t (Typ M c p)
    {-# REWRITE cns-typ #-}
    
    cns-η : {M : 𝕄} {M↓ : 𝕄↓ M} 
      → (t : 𝕋 M↓) (i : Idx M)
      → cns t (η M i) ↦ η↓ M↓ (idx t i)
    {-# REWRITE cns-η #-}

    cns-μ : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
      → (i : Idx M) (σ : Cns M i)
      → (δ : (p : Pos M σ) → Cns M (Typ M σ p))
      → cns t (μ M σ δ) ↦ μ↓ M↓ (cns t σ) (λ p → cns t (δ p))
    {-# REWRITE cns-μ #-}

    Slice𝕋 : {M : 𝕄} {M↓ : 𝕄↓ M}
      → 𝕋 M↓ → 𝕋 (Slice↓ M↓) 

  idxₛ : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
    → (f : Idxₛ M) → Idx↓ₛ M↓ f
  idxₛ t (i , c) = idx t i , cns t c

  cnsₛ : {M : 𝕄} {M↓ : 𝕄↓ M} (t : 𝕋 M↓)
    → (f : Idxₛ M) (σ : Cnsₛ M f)
    → Cns↓ₛ M↓ (idxₛ t f) σ
  cnsₛ {M} t .(i , η M i) (lf i) = lf↓ (idx t i)
  cnsₛ {M} t .(_ , μ M σ δ) (nd σ δ ε) =
    let δ↓ p = cns t (δ p)
        ε↓ p = cnsₛ t (Typ M σ p , δ p) (ε p)
    in nd↓ (cns t σ) δ↓ ε↓ 

  postulate

    Pb𝕋 : {M : 𝕄} {M↓ : 𝕄↓ M} (X : Idx M → Set)
      → (Y : (i : Idx M) → Idx↓ M↓ i → X i → Set)
      → (t : 𝕋 M↓) (ϕ : (i : Idx M) (x : X i) → Y i (idx t i) x)
      → 𝕋 (Pb↓ M↓ X Y) 

  Π𝕆 : {M : 𝕄} {M₁ : 𝕄↓ M}
    → {M₂ : 𝕄↓ (ΣM M M₁)}
    → (X : OpetopicType (ΣM M M₁))
    → (Y : OpetopicTypeOver M₂ X)
    → (t : 𝕋 M₂)
    → OpetopicType M  
  Ob (Π𝕆 {M} {M₁} {M₂} X Y t) i = (j : Idx↓ M₁ i) (x : Ob X (i , j)) → Ob↓ Y (i , j) (idx t (i , j)) x 
  Hom (Π𝕆 {M} {M₁} {M₂} X Y t) = Π𝕆 {Slice (Pb M C)}
    {Slice↓ (Pb↓ M₁ C (λ i j f → Ob X (i , j)))}
    {Slice↓ (Pb↓ M₂ _ λ { (i , j) k (f , x) → Ob↓ Y (i , j) k x  })}
    (OpType-map (Slice-map (Pb-map' (idmap (ΣM M M₁)) snd)) (Hom X))
    (OpType-map↓ (Slice-map↓ (Pb-map↓ (idmap↓ M₂) (idf _))) (Hom↓ Y))
    (Slice𝕋 (Pb𝕋 _ _ t λ { (i , j) (f , x) → f j x } )) 

    where C : Idx M → Set
          C i = (j : Idx↓ M₁ i) (x : Ob X (i , j)) → Ob↓ Y (i , j) (idx t (i , j)) x

  PullDown : (M : 𝕄) (M↓ : 𝕄↓ M)
    → (X : OpetopicType (ΣM M M↓))
    → (t : 𝕋 M↓)
    → OpetopicType M
  Ob (PullDown M M↓ X t) i = Ob X (i , idx t i)
  Hom (PullDown M M↓ X t) = PullDown
    (Slice (Pb M (λ i → Ob X (i , idx t i))))
    (Slice↓ (Pb↓ M↓ _ λ i j x → Ob X (i , j)))
    (OpType-map (Slice-map (Pb-map (λ _ → snd))) (Hom X))
    (Slice𝕋 (Pb𝕋 _ _ t λ i x → x))

  idx-Id : {A : Set} (x : A) (i : Idx IdMnd) → Idx↓ (IdMnd↓ A) i
  idx-Id x i = x

  cns-Id : {A : Set} (x : A) (i : Idx IdMnd)
    (c : Cns IdMnd i)
    → Cns↓ (IdMnd↓ A) {i = i} (idx-Id x i) c
  cns-Id x i c = ttᵢ

  Deco : (M : 𝕄) {f : Idx M} → Cns M f → (Idx M → Set) → Set
  Deco M σ A = (p : Pos M σ) → A (Typ M σ p)

  Deco↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {f : Idx M} {f↓ : Idx↓ M↓ f}
    → {σ : Cns M f} (σ↓ : Cns↓ M↓ f↓ σ)
    → {A : Idx M → Set} (A↓ : (i : Idx M) (i↓ : Idx↓ M↓ i) → A i → Set)
    → (ϕ : Deco M σ A)
    → Set
  Deco↓ {M} M↓ {σ = σ} σ↓ A↓ ϕ = (p : Pos M σ) → A↓ (Typ M σ p) (Typ↓ M↓ σ↓ p) (ϕ p)  

  postulate
    Id𝕋 : {A : Set} → A → 𝕋 (IdMnd↓ A)

    idx-Id-rew : {A : Set} (x : A) (i : Idxᵢ)
      → idx (Id𝕋 x) i ↦ idx-Id x i
    {-# REWRITE idx-Id-rew #-}

    cns-Id-rew : {A : Set} (x : A) (i : Idx IdMnd) (c : Cns IdMnd i)
      → cns (Id𝕋 x) {i = i} c ↦ cns-Id x i c
    {-# REWRITE cns-Id-rew #-}
  {-  
    Lift' : {M : 𝕄} → 𝕄↓ M → Set

    cns-lift : {M : 𝕄} {M↓ : 𝕄↓ M}
      → (l : Lift' M↓)
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → (σ : Cns M f)
      → Cns↓ M↓ f↓ σ

    cns-lift-fill : {M : 𝕄} {M↓ : 𝕄↓ M}
      → (l : Lift' M↓)
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → (σ : Cns M f)
      → Cns↓ (Slice M↓) f↓ σ
-}

    Lift' : (M : 𝕄)
      → (A : Idx M → Set)
      → (W : Idxₛ (Pb M A) → Set)
      → Set
{-
    cns-lift : {M : 𝕄}
      → (A : Idx M → Set)
      → (W : Idxₛ (Pb M A) → Set)
      → (l : Lift' M A W)
      → {f : Idx M} (σ : Cns M f)
      → (τ : A f)
      → Deco M σ A

    cns-lift-fill : {M : 𝕄}
      → (A : Idx M → Set)
      → (W : Idxₛ (Pb M A) → Set)
      → (l : Lift' M A W)
      → {f : Idx M}
      → (σ : Cns M f) (τ : A f)
      → W ((f , τ) , σ , cns-lift A W l σ τ)
-}
    Lift↓' : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {A : Idx M → Set} (A↓ : (i : Idx M) → Idx↓ M↓ i → A i → Set)
      → {W : Idxₛ (Pb M A) → Set}
      → (W↓ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M↓ A A↓) i → W i → Set)
      → Set

    cns-lift↓ : {M : 𝕄} {M↓ : 𝕄↓ M}
      → {A : Idx M → Set} (A↓ : (i : Idx M) → Idx↓ M↓ i → A i → Set)
      → {W : Idxₛ (Pb M A) → Set}
      → (W↓ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M↓ A A↓) i → W i → Set)
      → (l : Lift↓' M↓ A↓ W↓)
      → {f : Idxₚ M A} (f↓ : Idx↓ₚ M↓ A A↓ f)
      → (σ : Cnsₚ M A f)
      → Cns↓ₚ M↓ A A↓ f↓ σ

    cns-lift-fill↓ : {M : 𝕄} {M↓ : 𝕄↓ M}
      → {A : Idx M → Set} (A↓ : (i : Idx M) → Idx↓ M↓ i → A i  → Set)
      → {W : Idxₛ (Pb M A) → Set}
      → (W↓ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M↓ A A↓) i → W i → Set)
      → (l : Lift↓' M↓ A↓ W↓)
      → {f : Idxₚ M A} (f↓ : Idx↓ₚ M↓ A A↓ f)
      → (σ : Cnsₚ M A f)
      → (w : W (f , σ))
      → W↓ (f , σ) (f↓ , cns-lift↓ A↓ W↓ l f↓ σ) w
{-
    cns-lift↓2 : {M : 𝕄} {M↓ : 𝕄↓ M}
      → {A : Idx M → Set} (A↓ : (i : Idx M) → Idx↓ M↓ i → A i → Set)
      → {W : Idxₛ (Pb M A) → Set}
      → (W↓ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M↓ A A↓) i → W i → Set)
      → (l : Lift↓' M↓ A↓ W↓)
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → {σ : Cns M f} (σ↓ : Cns↓ M↓ f↓ σ)
      → {τ : A f} (τ↓ : A↓ f f↓ τ)
      → (ν : Deco M σ A)
      → Deco↓ M↓ σ↓ A↓ ν 

    cns-lift-fill↓2 : {M : 𝕄} {M↓ : 𝕄↓ M}
      → {A : Idx M → Set} (A↓ : (i : Idx M) → Idx↓ M↓ i → A i → Set)
      → {W : Idxₛ (Pb M A) → Set}
      → (W↓ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M↓ A A↓) i → W i → Set)
      → (l : Lift↓' M↓ A↓ W↓)
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → {σ : Cns M f} (σ↓ : Cns↓ M↓ f↓ σ)
      → {τ : A f} (τ↓ : A↓ f f↓ τ)
      → (ν : Deco M σ A)
      → (w : W ((f , τ) , σ , ν))
      → W↓ ((f , τ) , σ , ν) ((f↓ , τ↓) , σ↓ , cns-lift↓2 A↓ W↓ l f↓ σ↓ τ↓ ν) w
-}
    cns-lift : {M : 𝕄} {M↓ : 𝕄↓ M}
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → (σ : Cns M f)
      → Cns↓ M↓ f↓ σ

    cns-lift-fill : {M : 𝕄} {M↓ : 𝕄↓ M}
      → {A : Idx M → Set} (A↓ : (i : Idx M) → Idx↓ M↓ i → A i  → Set)
      → {W : Idxₛ (Pb M A) → Set}
      → (W↓ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M↓ A A↓) i → W i → Set)
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → (σ : Cns M f)
      → W ((f , {!!}) , {!!})
      → W↓ {!!} {!!} {!!}
     


  cns-lift-pb : {M : 𝕄} {M↓ : 𝕄↓ M}
    → {A : Idx M → Set} {A↓ : (i : Idx M) → Idx↓ M↓ i → A i → Set} 
    → {f : Idxₚ M A} (f↓ : Idx↓ₚ M↓ A A↓ f)
    → (σ : Cnsₚ M A f)
    → Cns↓ₚ M↓ A A↓ f↓ σ
  cns-lift-pb (f↓ , x) (σ , ν) = {!!} , {!!}

{-
    cns-lift2 : {M : 𝕄} {M↓ : 𝕄↓ M}
      → {A : Idxₛ M → Set} (A↓ : (i : Idxₛ M) → Idx↓ₛ M↓ i → A i  → Set)
      → {W : Idxₛ (Pb (Slice M) A) → Set}
      → (W↓ : (i : Idxₛ (Pb (Slice M) A)) → Idx↓ₛ (Pb↓ (Slice↓ M↓) A A↓) i → W i → Set)
      → (l : Lift'' (Slice↓ M↓) A↓ W↓)
      → {f : Idxₚ (Slice M) A} (f↓ : Idx↓ₚ (Slice↓ M↓) A A↓ f)
      → (σ : Cnsₚ (Slice M) A f)
      → Cns↓ₚ (Slice↓ M↓) A A↓ f↓ σ

    cns-lift-fill2 : {M : 𝕄} {M↓ : 𝕄↓ M}
      → {A : Idxₛ M → Set} (A↓ : (i : Idxₛ M) → Idx↓ₛ M↓ i → A i  → Set)
      → {W : Idxₛ (Pb (Slice M) A) → Set}
      → (W↓ : (i : Idxₛ (Pb (Slice M) A)) → Idx↓ₛ (Pb↓ (Slice↓ M↓) A A↓) i → W i → Set)
      → (l : Lift'' (Slice↓ M↓) A↓ W↓)
      → {f : Idxₚ (Slice M) A} (f↓ : Idx↓ₚ (Slice↓ M↓) A A↓ f)
      → (σ : Cnsₚ (Slice M) A f)
      → (w : W (f , σ))
      → W↓ (f , σ) (f↓ , cns-lift2 A↓ W↓ l f↓ σ) w
-}
  record is-liftable {M : 𝕄} (X : OpetopicType M) : Set where
    coinductive
    field
      base-liftable : Lift' M (Ob X) (Ob (Hom X)) 
      hom-liftable : is-liftable (Hom X)
  open is-liftable

  record is-liftable↓ {M : 𝕄} {M↓ : 𝕄↓ M} {X : OpetopicType M} (Y : OpetopicTypeOver M↓ X) : Set where
    coinductive
    field
      base-liftable↓ : Lift↓' M↓ (Ob↓ Y) (Ob↓ (Hom↓ Y)) 
      hom-liftable↓ : is-liftable↓ (Hom↓ Y)
  open is-liftable↓

  cns-lift-id : (A : Set) {f : Idxᵢ}
    → (f↓ : Idx↓ (IdMnd↓ A) f) (σ : Cns IdMnd f)
    → Cns↓ᵢ A {u = f} f↓ σ
  cns-lift-id A f↓ σ = ttᵢ

  postulate
    Good : {M : 𝕄} → 𝕄↓ M → Set
    good-η : {M : 𝕄} {M↓ : 𝕄↓ M} → Good M↓
      → {f : Idx M} {f↓ : Idx↓ M↓ f}  (σ : Cns↓ M↓ f↓ (η M f))
      → η↓ M↓ f↓ == σ

   
  cns-lift-slc3 : {M : 𝕄} {M↓ : 𝕄↓ M}
    → (G : Good M↓)
    → {f : Idxₛ M} (f↓ : Idx↓ₛ M↓ f)
    → (σ : Cnsₛ M f)
    → Cns↓ₛ M↓ f↓ σ
  cns-lift-slc3 G f↓ (lf i) =
    let foo = lf↓ f↓
    in {!!}
  cns-lift-slc3 {M↓ = M↓} G f↓ (nd {i} c δ ε) =
    let foo : Cns↓ₛ M↓ (fst f↓ , {!!}) (nd c δ ε)
        foo = nd↓ {M↓ = M↓} (cns-lift {M↓ = M↓} (fst f↓) c) (λ p → cns-lift {!Typ M!} (δ p)) {!!}
    in {!!}

  module _ {M : 𝕄} (M↓ : 𝕄↓ M) where
{-
    frm-η : {f : Idx M} (f↓ : Idx↓ M↓ f) (σ↓ : Cns↓ M↓ f↓ (η M f))
      → Typ↓ M↓ σ↓ (η-pos M f) == f↓

    tree-η : {f : Idx M} (f↓ : Idx↓ M↓ f) (σ↓ : Cns↓ M↓ f↓ (η M f))
      → η↓ M↓ (Typ↓ M↓ σ↓ (η-pos M f)) == σ↓ [ (λ f↓ → Cns↓ M↓ f↓ (η M f)) ↓ frm-η f↓ σ↓ ]
-}
    η-lem : {f : Idx M} (f↓ : Idx↓ M↓ f) (σ↓ : Cns↓ M↓ f↓ (η M f)) (pd : Cns↓ₛ M↓ (f↓ , σ↓) (lf f))
      → η↓ M↓ f↓ == σ↓
    η-lem f↓ .(η↓ M↓ f↓) (lf↓ .f↓) = idp

    lf-lem : {f : Idx M} (f↓ : Idx↓ M↓ f) (σ↓ : Cns↓ M↓ f↓ (η M f)) (pd : Cns↓ₛ M↓ (f↓ , σ↓) (lf f))
      → lf↓ f↓ == pd [ (λ σ↓ → Pd↓ M↓ (f↓ , σ↓) (lf f)) ↓ η-lem f↓ σ↓ pd ]
    lf-lem f↓ .(η↓ M↓ f↓) (lf↓ .f↓) = idp

    tree-η : {f : Idxₛ M} (f↓ : Idx↓ₛ M↓ f) (σ↓ : Cns↓ₛ M↓ f↓ (ηₛ M f))
      → η↓ₛ M↓ f↓ == σ↓
    tree-η {f , c} (f↓ , .(μ↓ M↓ c↓ δ↓)) (nd↓ c↓ δ↓ ε↓) =
      let 
          
          δ₁=δ = λ= λ p → η-lem (Typ↓ M↓ c↓ p) (δ↓ p) (ε↓ p)
          ε₁=ε = λ=↓ _ λ p → lf-lem (Typ↓ M↓ c↓ p) (δ↓ p) (ε↓ p)

          p = apd (λ δ↓ →
            nd↓ (μ↓ M↓ c↓ δ↓) (λ p → η↓ M↓ (Typ↓ M↓ (μ↓ M↓ c↓ δ↓) p))
                (λ p → lf↓ (Typ↓ M↓ (μ↓ M↓ c↓ δ↓) p)))
            (! δ₁=δ)

          q = apd (λ { (δ↓ , ε↓) → nd↓ c↓ δ↓ ε↓ }) (pair= δ₁=δ ε₁=ε)
                |> ↓-ap-in _ fst
                |> transport (λ x → _ == _ [ _ ↓ x ]) (fst=-β δ₁=δ ε₁=ε)

      in transport (λ x → _ == _ [ _ ↓ x ]) (!-inv-l δ₁=δ) (p ∙ᵈ q)

  -- Faux
  pb-η : (M : 𝕄) (M↓ : 𝕄↓ M) (G : Good M↓) (A : Idx M → Set) (A↓ : (i : Idx M) → Idx↓ M↓ i → A i  → Set)
    → {f : Idxₚ M A} (f↓ : Idx↓ₚ M↓ A A↓ f) (σ↓ : Cns↓ₚ M↓ A A↓ f↓ (ηₚ M A f))
    → η↓ₚ M↓ A A↓ f↓ == σ↓
  pb-η M M↓ G A A↓ f↓ (c↓ , ν) =
    let foo : {!!}
        foo = {!!}
    in pair= (good-η G c↓) {!!}
    
  good-closed : (M : 𝕄) (M↓ : 𝕄↓ M) (G : Good M↓) (A : Idx M → Set)
    → (A↓ : (i : Idx M) (j : Idx↓ M↓ i) → A i → Set)
    → {f : Idx (Slice (Pb M A))} {f↓ : Idx↓ (Slice↓ (Pb↓ M↓ A A↓)) f}
    → (σ : Cns↓ (Slice↓ (Pb↓ M↓ A A↓)) f↓ (η (Slice (Pb M A)) f))
    → η↓ (Slice↓ (Pb↓ M↓ A A↓)) f↓ == σ 
  good-closed M M↓ G A A↓ σ↓ = tree-η _ _ _ 

  cns-lift-slc : {M : 𝕄} (M↓ : 𝕄↓ M) {f : Idxₛ M}
    → (f↓ : Idx↓ₛ M↓ f) (σ : Cnsₛ M f)
    → Cns↓ₛ M↓ f↓ σ
  
{-
  postulate
    cns-lift-slc-rew : {M : 𝕄} (M↓ : 𝕄↓ M) {f : Idxₛ M}
      → (f↓ : Idx↓ₛ M↓ f)
      → cns-lift-slc M↓ f↓ (ηₛ M f) ↦ η↓ₛ M↓ {!!}
 -}
  

  postulate
    cns-η2 : (M : 𝕄) (M↓ : 𝕄↓ M)
      → (f : Idx M) (f↓ : Idx↓ M↓ f)
      → Cns↓ M↓ f↓ (η M f) ↦ {!η↓ M↓ ?!}

    ηₛ-pos-typ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idxₛ M}
      → (p : Posₛ M (ηₛ M i))
      → Typₛ M (ηₛ M i) p ↦ i
    {-# REWRITE ηₛ-pos-typ #-}

    ηₛ-pos-typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {i : Idxₛ M} (i↓ : Idx↓ₛ M↓ i)
      → (p : Posₛ M (ηₛ M i))
      → Typ↓ₛ M↓ (η↓ₛ M↓ i↓) p ↦ i↓
    {-# REWRITE ηₛ-pos-typ↓ #-}

  cns-lift-slc {M} M↓ {f} (f↓ , σ↓) (lf i) =
    let foo : Pd↓ M↓ (f↓ , η↓ M↓ f↓) (lf i)
        foo = lf↓ f↓ 
    in transport (λ x → Pd↓ M↓ (_ , x) (lf i)) {!!} foo  -- transport (λ x → Pd↓ M↓ (_ , x) (lf i)) (tree-η' M↓ (fst f↓) (snd f↓)) foo -- transport (λ { (x , y) → Pd↓ M↓ (x , y) {!!} }) (pair= (frm-η _ f↓ {!!}) (tree-η _ f↓ {!!})) (lf↓ {!Typ!}) -- transport↓ (λ x → Pd↓ M↓ {!!} {!x!}) (frm-η {!!} {!!} {!!}) (tree-η (Slice↓ M↓) {!!} {!!}) {!!}
  cns-lift-slc {M} M↓ f↓ (nd c δ ε) = {!!}

  lem-contr-ctx : {A : Set} {B : A → Set} (C : (x : A) → B x → Set) 
    → (g : (x : A) → is-contr (B x))
    → {x y : A}
    → (p : x == y)
     → {x₁ : B x} {y₁ : B y}
    → (q : x₁ == y₁ [ B ↓ p ])
    → {x₂ : C x x₁} {y₂ : C y y₁}
    → (x₂ == y₂ [ uncurry C ↓ pair= p q  ])
       == (transport! (C x) (contr-path (g x) _) x₂ == transport! (C y) (contr-path (g y) _) y₂ [ (λ x → C x (contr-center (g x))) ↓ p ])
  lem-contr-ctx C g {x} idp {x₁} idp {x₂} {y₂} with contr-path (g x) x₁
  ... | idp = idp

  Pos-η-is-contr : (M : 𝕄) (i : Idx M) → is-contr (Pos M (η M i))
  Pos-η-is-contr M i =
    let ctr = η-pos M i
        pth = η-pos-elim M i (λ p → ctr == p) idp
    in has-level-in (ctr , pth)
    

  cns-lift-slc-with-tgt'' : {M : 𝕄} (M↓ : 𝕄↓ M)
    → (A : Idx M → Set) (A↓ : (i : Idx M) → Idx↓ M↓ i → A i  → Set)
    → (W : Idxₛ (Pb M A) → Set) (W↓ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M↓ A A↓) i → W i → Set)
    → (G : Good M↓)
    → (act : unique-action↓ M↓ A↓ W↓)
    → {f : Idxₚ M A} {σ : Cnsₚ M A f} {θ : W (f , σ)}
    → (f↓ : Idx↓ₚ M↓ A A↓ f)
    → (σ↓ : Cns↓ₚ M↓ A A↓ f↓ σ)
    --→ (σ' : Cnsₛ (Pb (Slice M) A) (f , σ))
    → (σ' : Cnsₚ (Slice (Pb M A)) W ((f , σ) , θ))
   -- → Σ (A↓ (fst f) (fst f↓) (snd f)) λ τ → Pd↓ (Pb↓ (Slice↓ M↓) A A↓) ((fst f↓ , τ) , σ↓) (fst σ')

    → Σ (A↓ (fst f) (fst f↓) (snd f)) λ τ↓ →
      Σ (W↓ (f , σ) ((fst f↓ , τ↓) , σ↓) θ) λ θ↓ →
        Cns↓ₚ (Slice↓ (Pb↓ M↓ A A↓)) W W↓ {i = (f , σ) , θ} (((fst f↓ , τ↓) , σ↓) , θ↓) σ'

  cns-lift-slc-with-tgt' : {M : 𝕄} (M↓ : 𝕄↓ M)
    → (A : Idx M → Set) (A↓ : (i : Idx M) → Idx↓ M↓ i → A i  → Set)
    → (W : Idxₛ (Pb M A) → Set) (W↓ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M↓ A A↓) i → W i → Set)
    → (G : Good M↓)
    → (act : unique-action↓ M↓ A↓ W↓)
    → {f : Idxₚ M A} {σ : Cnsₚ M A f} {θ : W (f , σ)}
    → (f↓ : Idx↓ₚ M↓ A A↓ f)
    → (σ↓ : Cns↓ₚ M↓ A A↓ f↓ σ)
    --→ (σ' : Cnsₛ (Pb (Slice M) A) (f , σ))
    → (σ' : Cnsₚ (Slice (Pb M A)) W ((f , σ) , θ))
   -- → Σ (A↓ (fst f) (fst f↓) (snd f)) λ τ → Pd↓ (Pb↓ (Slice↓ M↓) A A↓) ((fst f↓ , τ) , σ↓) (fst σ')

   → Σ (A↓ (fst f) (fst f↓) (snd f)) λ τ↓ →
     Σ (W↓ (f , σ) ((fst f↓ , τ↓) , σ↓) θ) λ θ↓ →
       Cns↓ₚ (Slice↓ (Pb↓ M↓ A A↓)) W W↓ {i = (f , σ) , θ} (((fst f↓ , τ↓) , σ↓) , θ↓) σ'
  cns-lift-slc-with-tgt' {M} M↓ A A↓ W W↓ G act {i , x} {σ , ν} {θ} (i↓ , x↓) (σ↓ , ν↓) (lf _ , _) = τ↓ , θ↓ , l , λ ()
    where α : η↓ M↓ i↓ == σ↓
          α = good-η G σ↓

          β : i↓ == Typ↓ M↓ σ↓ (η-pos M i)
          β = ap (λ σ↓ → Typ↓ M↓ σ↓ (η-pos M i)) α

          τ↓ : A↓ i i↓ x
          τ↓ = transport (λ f → A↓ i f x) (! β) (ν↓ (η-pos M i))

          ?? : W↓ ((i , x) , η M i , (λ _ → x)) ((i↓ , {!x↓!}) , σ↓ , ν↓) θ
          ?? = snd $ contr-center (act θ i↓ σ↓ ν↓)

          θ↓ : W↓ ((i , x) , η M i , (λ _ → x)) ((i↓ , τ↓) , σ↓ , ν↓) θ
          θ↓ = {!!}

          τ=ν↓ : (p p' : Pos M (η M i)) (q : p == p' [ (λ _ → Pos M (η M i)) ↓ α ])
            → τ↓ == ν↓ p' [ (λ { (σ↓ , p) → A↓ i (Typ↓ M↓ σ↓ p) x }) ↓ pair= α q ]
          τ=ν↓ =
            let aux q = coe! (lem-contr-ctx _ (λ _ → Pos-η-is-contr M i) α q)
                        $ ↓-ap-out (λ y → A↓ i y x)
                                   (λ σ↓ → Typ↓ M↓ σ↓ (η-pos M i))
                                   α
                                   (transp-↓ (λ y → A↓ i y x) β (ν↓ (η-pos M i)))
                                 
            in η-pos-elim M i (λ p → (p' : Pos M (η M i))
                   → (q : p == p' [ (λ _ → Pos M (η M i)) ↓ α ])
                   → τ↓ == ν↓ p' [ (λ { (σ↓ , p) → A↓ i (Typ↓ M↓ σ↓ p) x }) ↓ pair= α q ])
                 $ η-pos-elim M i (λ p' → (q : η-pos M i == p' [ (λ _ → Pos M (η M i)) ↓ α ])
                       → τ↓ == ν↓ p' [ (λ { (σ↓ , p) → A↓ i (Typ↓ M↓ σ↓ p) x }) ↓ pair= α q ]) aux
                 

          ι : η↓ₚ M↓ A A↓ (i↓ , τ↓) == σ↓ , ν↓
          ι = pair= α (↓-Π-in (τ=ν↓ _ _))

          l : Pd↓ (Pb↓ M↓ A A↓) ((i↓ , τ↓) , σ↓ , ν↓) (lf (i , x))
          l = transport (λ y → Pd↓ (Pb↓ M↓ A A↓) ((i↓ , τ↓) , y) (lf (i , x))) ι (lf↓ (i↓ , τ↓))  
  cns-lift-slc-with-tgt' {M} M↓ A A↓ W W↓ G act {i , x} {σ , ν} {θ} (i↓ , x↓) (σ↓ , ν↓) (nd c δ ε , ν↓₁) =
    let y = ν↓₁ true

        w : W ((i , x) , μ M (fst c) (λ p → fst (δ p)) , (λ p →
          snd (δ (μ-pos-fst M (fst c) (λ p₁ → fst (δ p₁)) p))
          (μ-pos-snd M (fst c) (λ p₁ → fst (δ p₁)) p)))
        w = θ

        τ↓ : A↓ i i↓ x
        τ↓ = fst $ contr-center (act θ i↓ σ↓ ν↓)
    in τ↓ , {!!} , {!!} , {!!}
    
  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

  module _ {M : 𝕄} {M₁ : 𝕄↓ M}
    {M₂ : 𝕄↓ (ΣM M M₁)}
    (X : OpetopicType (ΣM M M₁))
    (Y : OpetopicTypeOver M₂ X)
    (t : 𝕋 M₂) where

    Tree-ap : {f : Idx M} {σ : Cns M f}
      → (δ : (p : Pos M σ) → Ob (Π𝕆 {M₁ = M₁} X Y t) (Typ M σ p)) 
      → (δa : (p : Pos M σ) → Σ (Idx↓ M₁ (Typ M σ p)) λ j → Ob X (Typ M σ p , j))
      → (p : Pos M σ)
      → Ob↓ Y (Typ M σ p , fst (δa p)) (idx t (Typ M σ p , fst (δa p))) (snd (δa p))
    Tree-ap δ δa p = δ p (fst (δa p)) (snd (δa p))


  module _ (M : 𝕄) (A : Idxₛ M → Set) (M↓ : 𝕄↓ M) (A↓ : (f : Idxₛ M) → Idx↓ₛ M↓ f → A f → Set) where

    --μ-lem : (f↓ : Idx↓ₛ M↓ (f , μ M σ δ)) →

    

    tree-lift : {A : Idx M → Set} (A↓ : (i : Idx M) → Idx↓ M↓ i → A i  → Set)
      → {W : Idxₛ (Pb M A) → Set} (W↓ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M↓ A A↓) i → W i → Set) 
      → {f : Idxₚ M A} {σ : Cnsₚ M A f} {δ : (p : Posₚ M A {i = f} σ) → Cnsₚ M A (Typₚ M A σ p)} {ε : (p : Posₚ M A σ) → Pd (Pb M A) (Typₚ M A σ p , δ p)}
      → {ν : (p : Posₛ (Pb M A) (nd σ δ ε)) → W (Typₛ (Pb M A) (nd σ δ ε) p)}
      → (θ : W (_ , μ (Pb M A) σ δ))
      → (f↓ : Idx↓ₚ (Slice↓ (Pb↓ M↓ A A↓)) W W↓ ((_ , μ (Pb M A) σ δ) , θ)) 
      → Cns↓ₚ (Slice↓ (Pb↓ M↓ A A↓)) W W↓ f↓ (nd σ δ ε , ν)
    tree-lift = {!!}
{-
  Π𝕆-is-fibrant : (M : 𝕄) (M₁ : 𝕄↓ M)
    → (A : Idx M → Set) (A₁ : (i : Idx M) → Idx↓ M₁ i → A i  → Set)
    → (W : Idxₛ (Pb M A) → Set) (W₁ : (i : Idxₛ (Pb M A)) → Idx↓ₛ (Pb↓ M₁ A A₁) i → W i → Set)
    → (M₂ : 𝕄↓ (ΣM (Slice (Pb M A)) (Slice↓ (Pb↓ M₁ A A₁))))
    → (X : OpetopicType (ΣM (Slice (Pb M A)) (Slice↓ (Pb↓ M₁ A A₁))))
    → (Y : OpetopicTypeOver M₂ X)
    → (t₁ : 𝕋 M₁)
    → (t : 𝕋 M₂)
    → (X-fib : is-fibrant X)
    → (Y-fib : is-fibrant↓ Y)
    → is-fibrant (Π𝕆 {M₁ = Slice↓ (Pb↓ M₁ A A₁)} X Y t)
  base-fibrant (Π𝕆-is-fibrant M M₁ A A₁ W W₁ M₂ X Y t₁ t X-fib Y-fib) .(i , η M (fst i) , (λ _ → snd i)) (lf i) ν = {!!}
  base-fibrant (Π𝕆-is-fibrant M M₁ A A₁ W W₁ M₂ X Y t₁ t X-fib Y-fib) .(_ , μ M (fst c) (λ p → fst (δ p)) , (λ p → snd (δ (μ-pos-fst M (fst c) (λ p₁ → fst (δ p₁)) p)) (μ-pos-snd M (fst c) (λ p₁ → fst (δ p₁)) p))) (nd c δ ε) ν =
    let foo = {!!}

        h : (j : Idx↓ₛ (Pb↓ (Slice↓ (Pb↓ M₁ A A₁)) (Pi.C X Y t) (λ i₁ j₁ f → Ob X (i₁ , j₁))) (((i , μₚ M (λ z → A z) c (λ p → δ p)) , ?19) , nd c δ ε , ν))
        h = {!!}
    in has-level-in (({!!} , {!!}) , {!!})
  hom-fibrant (Π𝕆-is-fibrant M M₁ A A₁ W W₁ M₂ X Y t₁ t X-fib Y-fib) = {!!}
-}


  ↓-to-Σ : {M : 𝕄} {M↓ : 𝕄↓ M}
    → (X : OpetopicTypeOver M↓ (Terminal M))
    → OpetopicType (ΣM M M↓)
  Ob (↓-to-Σ X) (i , i↓) = Ob↓ X i i↓ tt
  Hom (↓-to-Σ {M} {M↓} X) =
    let foo = ↓-to-Σ {Slice (Pb M (Ob (Terminal M)))} {Slice↓ (Pb↓ M↓ (Ob (Terminal M)) (Ob↓ X))} (Hom↓ X)
    in {!!}

  unique-lift : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {A : Idxₛ M → Set} (A↓ : (i : Idxₛ M) → Idx↓ₛ M↓ i → A i  → Set)
    → {W : Idxₛ (Pb (Slice M) A) → Set} (W↓ : (i : Idxₛ (Pb (Slice M) A)) → Idx↓ₛ (Pb↓ (Slice↓ M↓) A A↓) i → W i → Set)
    → (a : unique-action↓ (Slice↓ M↓) A↓ W↓)
    → {i : Idxₚ (Slice M) A } (i↓ : Idx↓ₚ (Slice↓ M↓) A A↓ i)
    → (pd : Cnsₚ (Slice M) A i)
    → is-contr (Cns↓ₚ (Slice↓ M↓) A A↓ i↓ pd)
  unique-lift = {!!}

  Π𝕆-is-fibrant : {M : 𝕄} {M₁ : 𝕄↓ M}
    → {M₂ : 𝕄↓ (ΣM M M₁)}
    → (X : OpetopicType (ΣM M M₁))
    → (Y : OpetopicTypeOver M₂ X)
    → (t : 𝕋 M₂)
    → (X-fib : is-fibrant X)
    → (Y-fib : is-fibrant↓ Y)
    → (l : is-liftable X)
    → is-fibrant (Π𝕆 {M₁ = M₁} X Y t)
  base-fibrant (Π𝕆-is-fibrant {M} {M₁} {M₂} X Y t X-fib Y-fib l) f σ ν =
    let h : (i↓ : Idx↓ M₁ f) (x : Ob X (f , i↓))
            → is-contr (Σ (Ob↓ Y (f , i↓) (idx t _) x) λ y →
                          Ob↓ (Hom↓ Y) (((f , i↓) , x) , (σ , {!!}) , (λ p → {!!})) ((idx t _ , y) , cns t _ , {!!}) {!θ!})
        h i↓ x =
          let σν₂' : Cns↓ₚ {M = M} M₁ (λ _ → ⊤) (λ i i↓ _ → Ob X (i , i↓)) {i = f , tt} (i↓ , x) (σ , λ _ → tt)
              σν₂' = cns-lift {M = Pb M (cst ⊤)} {M↓ = Pb↓ M₁ (cst ⊤) (λ i i↓ _ → Ob X (i , i↓))}
                    {f = f , tt} (i↓ , x) (σ , cst tt)

              σν₂ : Cns↓ₚ {M = M} M₁ (λ _ → ⊤) (λ i i↓ _ → Ob X (i , i↓)) {i = f , tt} (i↓ , x) (σ , λ _ → tt)
              σν₂ = cns-lift↓ {M↓ = M₁} {A = λ _ → ⊤} (λ i i↓ _ → Ob X (i , i↓))
                      {W = λ _ → ⊤}
                      (λ { ((i , _) , σ , ν) ((i↓ , x) , (σ↓ , ν↓)) _ →
                        Ob (Hom X) (((i , i↓) , x) , (σ , σ↓) , ν↓) }) {!base-liftable $ l!} (i↓ , x) (σ , cst tt) 

              σ₁ : Cns↓ M₁ i↓ σ
              σ₁ = fst σν₂

              ν₁ : Deco (ΣM M M₁) (σ , σ₁) (Ob X)
              ν₁ = snd σν₂

              --σ₂' : Cns↓ M₂ (idx t (f , i↓)) (σ , σ₁)
              --σ₂' = cns-lift {M = ΣM M M₁} {M↓ = M₂} (idx t (f , i↓)) (σ , σ₁)


              σ₂ : Cns↓ M₂ (idx t (f , i↓)) (σ , σ₁)
              σ₂ = cns t (σ , σ₁)

              ν₂ = Deco M σ (Ob (Π𝕆 {M₁ = M₁} X Y t))
              ν₂ p = ν p (Typ↓ M₁ σ₁ p) (ν₁ p)

              θ : Ob (Hom X) (((f , i↓) , x) , (σ , σ₁) , ν₁)
              θ = cns-lift-fill↓ {M↓ = M₁} {A = λ _ → ⊤} (λ i i↓ _ → Ob X (i , i↓))
                      {W = λ _ → ⊤}
                      (λ { ((i , _) , σ , ν) ((i↓ , x) , (σ↓ , ν↓)) _ →
                        Ob (Hom X) (((i , i↓) , x) , (σ , σ↓) , ν↓) }) {!!} (i↓ , x) (σ , cst tt)
                      tt

              foo : is-contr (Σ (Ob↓ Y (f , i↓) (idx t _) x) λ y →
                                Ob↓ (Hom↓ Y) (((f , i↓) , x) , (σ , σ₁) , ν₁)
                                             ((idx t _ , y) , cns t _ , ν₂)
                                             θ)
              foo = base-fibrant↓ Y-fib θ (idx t (f , i↓)) σ₂ ν₂
          in foo

        C : Idx M → Set
        C i = (j : Idx↓ M₁ i) (x : Ob X (i , j)) → Ob↓ Y (i , j) (idx t (i , j)) x

        τ : (i↓ : Idx↓ M₁ f) (x : Ob X (f , i↓)) → Ob↓ Y (f , i↓) (idx t (f , i↓)) x
        τ = λ i↓ x → fst $ contr-center $ h i↓ x

        
        HomX = OpType-map (Slice-map (Pb-map' (idmap (ΣM M M₁)) {A = Ob-Σ M M₁
         (λ z →
            (j : Idx↓ M₁ z) (x : Ob X (z , j)) →
            Ob↓ Y (z , j) (idx t (z , j)) x)
         (λ z z₁ i → Ob X (z , z₁))} snd)) (Hom X)
        HomY = OpType-map↓ (Slice-map↓ (Pb-map↓ (idmap↓ M₂) (idf _))) (Hom↓ Y)

        k : (i : Idx↓ (Slice↓ (Pb↓ M₁ C (λ i j f → Ob X (i , j)))) ((f , τ) , σ , ν))
            (x : Ob {M = Slice (Pb (ΣM M M₁) (Ob-Σ M M₁ C λ i j _ → Ob X (i , j)))} HomX
                    (((f , (fst $ fst i)) , τ , (snd $ fst i)) , (σ , (fst $ snd i)) , λ p → ν p , (snd $ snd i) p))
            → Ob↓ {M↓ = Slice↓ (Pb↓ M₂ (Ob-Σ M M₁ C λ i j _ → Ob X (i , j)) λ { (i , j) k (f , x) → Ob↓ Y (i , j) k x  })}
                   HomY (((f , (fst $ fst i)) , τ , (snd $ fst i)) , (σ , (fst $ snd i)) , λ p → ν p , (snd $ snd i) p)
                   ((idx t (f , fst (fst i)) , τ (fst (fst i)) (snd (fst i))) , cns t (σ , fst (snd i)) , (λ p → ν p (Typ↓ M₁ {!!} p) (snd (snd i) p)))
                   x   
        k i x = {!!}
         
        
    in has-level-in ((τ , {!!}) , {!!})
  hom-fibrant (Π𝕆-is-fibrant X Y t X-fib Y-fib l) = {!!}

  

    {-
  Π𝕆-is-fibrant : (M : 𝕄) (M₁ : 𝕄↓ M)
    → (M₂ : 𝕄↓ (ΣM M M₁))
   -- → (X : Opetopic)
    → (X : OpetopicTypeOver M1 (ΣM M M₁))
    → (Y : OpetopicTypeOver M₂ ?)
 --   → (t₁ : 𝕋 M₁)
    → (t : 𝕋 M₂)
    → (X-fib : is-fibrant X)
    → (Y-fib : is-fibrant↓ Y)
    → (l : {!is-liftable X!}) -- Lift'' ? ?) 
    → is-fibrant (Π𝕆 {M₁ = M₁} X Y t)
  base-fibrant (Π𝕆-is-fibrant M M₁ M₂ X Y t X-fib Y-fib l) i σ ν =
    let 

        νy : (p : Pos-Σ M M₁ (σ , {!!})) → Ob↓ Y (Typ-Σ M M₁ (σ , {!cns t₁ σ!}) p) {!!} ({!!} p)
        νy p = ν p {!!} {!!}

        

        h : (i↓ : Idx↓ M₁ i) (x : Ob X (i , i↓)) → Ob↓ Y (i , i↓) (idx t (i , i↓)) x
        h i↓ x =
          let σ↑ : Cns↓ M₁ i↓ σ
              σ↑ = {!!} --cns-lift l i↓ σ

              σ↑' : Cns↓ₚ M₁ (Ob (Π𝕆 {M₁ = M₁} X Y t)) (λ i i↓ _ → Ob X (i , i↓)) (i↓ , x) (σ , ν)
              σ↑' = {!cns!}


              νx : (p : Pos-Σ M M₁ (σ , σ↑)) → Ob X (Typ-Σ M M₁ (σ , σ↑) p)
              νx p = {!!}
          in fst $ contr-center (base-fibrant↓ Y-fib {σ = σ , σ↑} {ν = νx} {!!} {!!} {!!} νy)
    in has-level-in ((h , {!!}) , {!!})
  {-  let σa : (p : Pos M σ) → Σ (Idx↓ M₁ (Typ M σ p)) λ j → Ob X (Typ M σ p , j)
        σa = {!!}

        σ' : (p : Pos M σ) → Ob↓ Y (Typ M σ p , fst (σa p)) (idx t (Typ M σ p , fst (σa p))) (snd (σa p))
        σ' = Tree-ap {M₁ = M₁} X Y t ν σa

        σ'' : (p : Pos-Σ M M₁ (σ , {!Cnsₛ-lift ? ? ?!})) → Ob↓ Y (Typ-Σ M M₁ (σ , {!!}) p) (idx t (Typ M σ p , fst (σa p))) (snd (σa p))
        σ'' = Tree-ap {M₁ = M₁} X Y t ν σa

        h : (j : Idx↓ M₁ f) (x : Ob X (f , j)) → Ob↓ Y (f , j) (idx t (f , j)) x
        h j x = fst $ contr-center (base-fibrant↓ Y-fib {σ = σ , {!!}} {ν = {!!}} {!!} {!!} {!!} σ'') 
        ctr = h , {!!} 
    in has-level-in (ctr , {!!}) -}
  hom-fibrant (Π𝕆-is-fibrant M M₁ M₂ X Y t₁ t X-fib Y-fib) = {!!}
-}
  Π𝕆-is-fibrant4 : (A : Set) (B : A → Set)
    → (X : OpetopicType (ΣM (ΣM IdMnd (IdMnd↓ A)) {!Ext ?!}))
    → (Y : OpetopicTypeOver (Ext _ (B ∘ snd)) X)
   -- → (t₁ : 𝕋 M₁)
    → (t : 𝕋 _)
    → (X-fib : is-fibrant X)
    → (Y-fib : is-fibrant↓ Y)
    → is-fibrant (Π𝕆 {M₁ = IdMnd↓ A} {!!} {!!} t)
  

  Π𝕆-is-fibrant3 : (A : Set) (B : A → Set)
    → (X : OpetopicType (ΣM IdMnd (IdMnd↓ A)))
    → (Y : OpetopicTypeOver (Ext _ (B ∘ snd)) X)
   -- → (t₁ : 𝕋 M₁)
    → (t : 𝕋 _)
    → (X-fib : is-fibrant X)
    → (Y-fib : is-fibrant↓ Y)
    → is-fibrant (Π𝕆 {M₁ = IdMnd↓ A} X Y t)
  base-fibrant (Π𝕆-is-fibrant3 A B X Y t X-fib Y-fib) ttᵢ ttᵢ ν = has-level-in (((λ i↓ x → fst $ contr-center $ kk i↓ x) , {!λ i↓ x → snd $ k i↓ x!}) , {!!})
    where --h : (i↓ : Idx↓ᵢ A ttᵢ) (x : Ob X (ttᵢ , i↓))
          --    → Ob↓ Y (ttᵢ , i↓) (idx t (ttᵢ , i↓)) x
          --h i↓ x = ν _ i↓ x

          err : (i↓ : Idx↓ᵢ A ttᵢ) (x : Ob X (ttᵢ , i↓)) → {!!}
          err i↓ x = {!!}
            where x↓ : {!Ob X (ttᵢ , i)!}
                  x↓ = {!!}

                  θ : Ob (Hom X) (((ttᵢ , i↓) , x) , (ttᵢ , ttᵢ ) , λ _ → x)
                  θ = {!!}

          invv : Ob (Hom X) {!!}
          invv = {!!}

          g : (i↓ : Idx↓ᵢ A ttᵢ) (x : Ob X (ttᵢ , i↓)) → is-contr (Σ (Ob X (ttᵢ , i↓)) λ x₁ → Ob (Hom X) (((ttᵢ , i↓) , x₁) , (ttᵢ , ttᵢ) , λ _ → x))
          g i↓ x = base-fibrant X-fib (ttᵢ , i↓) (ttᵢ , ttᵢ) (λ _ → x)

          k : (i↓ : Idx↓ᵢ A ttᵢ) (x : Ob X (ttᵢ , i↓))
              → {!!} -- is-contr (Σ (Ob↓ Y (ttᵢ , i↓) (idx t (ttᵢ , i↓)) {!!}) λ y →
                    --        Ob↓ (Hom↓ Y) (((ttᵢ , i↓) , {!!}) , (ttᵢ , ttᵢ) , (λ _ → {!!}))
                      --                   {!!} --((idx t (ttᵢ , i↓) , y) , (λ _ → idx t (ttᵢ , i↓)) , λ _ → ν ttᵢ i↓ {!!})
                        --                 {!snd $ coe (contr-path (g i↓ x) ?) ? !})
          k i↓ x =
            let τₓ = fst $ contr-center $ g i↓ {!!}
            in base-fibrant↓ Y-fib {f = ttᵢ , i↓} {ttᵢ , ttᵢ} {λ _ → {!!}} {{!τₓ!}} {!snd (g i↓ x)!}
                                          {!!} {!!} {!!} --(idx t (_ , i↓)) (λ _ → idx t (ttᵢ , i↓)) λ _ → ν ttᵢ i↓ {!!} 

          kk : (i↓ : Idx↓ᵢ A ttᵢ) (x : Ob X (ttᵢ , i↓)) → is-contr (Σ (Ob↓ Y (ttᵢ , i↓) (idx t (ttᵢ , i↓)) {!!}) λ y →
                                                                    Ob↓ (Hom↓ Y) (((ttᵢ , i↓) , {!!}) , (ttᵢ , ttᵢ) , (λ _ → {!!}))
                                                                                 ((idx t (ttᵢ , i↓) , y) , (λ _ → idx t (ttᵢ , i↓)) , λ _ → ν ttᵢ i↓ {!!})
                                                                                 {!!})
          kk i↓ x =
            let τₓ = fst $ contr-center $ g i↓ {!!}
            in base-fibrant↓ Y-fib {f = ttᵢ , i↓} {ttᵢ , ttᵢ} {λ _ → {!!}} {τ = x} ({! snd $ contr-center (g i↓ x) !}) {!!} {!!} {!!}

  hom-fibrant (Π𝕆-is-fibrant3 A B X Y t X-fib Y-fib) = {!!}
