{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import Monad
open import MonadOver
open import UniCat
open import Delta
open import OpetopicType
open import IdentityMonad
open import Pb
open import HoTT
open import IdentityMonadOver
open import MonadEqv

module Categories where

  postulate
    η-pos-typₛ : (M : 𝕄) (i : Idxₛ M)
      → (p : Posₛ M (ηₛ M i))
      → Typₛ M {i = i} (ηₛ M i) p ↦ i
    {-# REWRITE η-pos-typₛ #-}

    η-pos-typₛₚ : let M  = IdMnd in (A : Idx M → Set) (i : Idxₛ (Pb M A))
      → (p : Posₛ (Pb M A) (ηₛ (Pb M A) i))
      → Typₛ (Pb M A) {i = i} (ηₛ (Pb M A) i) p ↦ i
    {-# REWRITE η-pos-typₛₚ #-}

    μ-pos-typₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
      → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
      → (p : Posₛ M (μₛ M c δ))
      → Typₛ M (μₛ M c δ) p ↦ Typₛ M (δ (μ-pos-fstₛ M c δ p)) (μ-pos-sndₛ M c δ p)
    {-# REWRITE μ-pos-typₛ #-}

    μ-pos-fst-βₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
      → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
      → (p : Posₛ M c) (q : Posₛ M (δ p))
      → μ-pos-fstₛ M c δ (μ-posₛ M c δ p q) ↦ p
    {-# REWRITE μ-pos-fst-βₛ #-}

    μ-pos-snd-βₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
      → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
      → (p : Posₛ M c) (q : Posₛ M (δ p))
      → μ-pos-sndₛ M c δ (μ-posₛ M c δ p q) ↦ q
    {-# REWRITE μ-pos-snd-βₛ #-}

    μ-pos-ηₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
      → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
      → (p : Posₛ M (μₛ M c δ))
      → μ-posₛ M c δ (μ-pos-fstₛ M c δ p) (μ-pos-sndₛ M c δ p) ↦ p
    {-# REWRITE μ-pos-ηₛ #-}
    
    -- μ laws
    μ-unit-rightₛ : (M : 𝕄) (i : Idxₛ M)
      → (c : Cnsₛ M i)
      → μₛ M c (λ p → ηₛ M (Typₛ M c p)) ↦ c
    {-# REWRITE μ-unit-rightₛ #-}

    μ-unit-leftₛ : (M : 𝕄) (i : Idxₛ M) 
      → (δ : (p : Posₛ M (ηₛ M i)) → Cnsₛ M i)
      → μₛ M (ηₛ M i) δ ↦ δ (η-posₛ M i)
    --{-# REWRITE μ-unit-leftₛ #-}

    μ-assocₛ : (M : 𝕄) {i : Idxₛ M} (c : Cnsₛ M i)
      → (δ : (p : Posₛ M c) → Cnsₛ M (Typₛ M c p))
      → (ε : (p : Posₛ M (μₛ M c δ)) → Cnsₛ M (Typₛ M (μₛ M c δ) p))
      → μₛ M (μₛ M c δ) ε ↦ μₛ M c (λ p → μₛ M (δ p) (λ q → ε (μ-posₛ M c δ p q)))
    {-# REWRITE μ-assocₛ #-}

    γ-assoc : (M : 𝕄) {i : Idx M} {c : Cns M i} 
      → (ρ : Cnsₛ M (i , c))
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M c) → Cnsₛ M (Typ M c p , δ p))
      → (δ₁ : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p))
      → (ε₁ : (p : Pos M (μ M c δ)) → Cnsₛ M (Typ M (μ M c δ) p , δ₁ p))
      → γ M (γ M ρ δ ε) δ₁ ε₁ ↦ γ M ρ (λ p → μ M (δ p) (δ₁ ∘ μ-pos M c δ p)) λ p → γ M (ε p) (δ₁ ∘ μ-pos M c δ p) (ε₁ ∘ μ-pos M c δ p)
    {-# REWRITE γ-assoc #-}

    γ-unit-r : (M : 𝕄) {i : Idx M} {c : Cns M i} 
      → (ρ : Cnsₛ M (i , c))
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M c) → Cnsₛ M (Typ M c p , δ p))
      → γ M ρ (λ p → η M (Typ M c p)) (λ p → lf (Typ M c p)) ↦ ρ
    {-# REWRITE γ-unit-r #-}

    typ-γ-pos-inr : (A : ⊤ → Set) → let M = Pb IdMnd A in {i : Idx M} {c : Cns M i} 
      → (ρ : Cnsₛ M (i , c))
      → (δ : (p : Pos M {i} c) → Cns M (Typ M {i} c p))
      → (ε : (p : Pos M {i} c) → Cnsₛ M (Typ M {i} c p , δ p))
      → (p : Pos M {i} c) (q : Posₛ M (ε p))
      → Typₛ M (γ M ρ δ ε) (γ-pos-inr M ρ δ ε p q) ↦ Typₛ M (ε p) q
    {-# REWRITE typ-γ-pos-inr #-}

    typ-γ-pos-inl : (A : ⊤ → Set) → let M = Pb IdMnd A in {i : Idx M} {c : Cns M i} 
      → (ρ : Cnsₛ M (i , c))
      → (δ : (p : Pos M {i} c) → Cns M (Typ M {i} c p))
      → (ε : (p : Pos M {i} c) → Cnsₛ M (Typ M {i} c p , δ p))
      → (p : Posₛ M ρ)
      → Typₛ M (γ M ρ δ ε) (γ-pos-inl M ρ δ ε p) ↦ Typₛ M ρ p
    {-# REWRITE typ-γ-pos-inl #-}

  ∞-category : Set (lsucc lzero)
  ∞-category = Σ (OpetopicType IdMnd) (is-fibrant ∘ Hom)

  1-category : Set (lsucc lzero)
  1-category = Σ ∞-category λ { (X , fib) → (i : Idxₛ (Pb IdMnd (Ob X))) → is-set (Ob (Hom X) i) } 

  module _ (C : 1-category) where

    private
      X = fst (fst C)
      fib = snd (fst C)
      hom-sets = snd C

    comp-has-all-paths : {x y z : Obj X}
      → {f : Arrow X x y} {g : Arrow X y z}
      → {h h₁ : Arrow X x z}
      → (θ : Simplex X f g h)
      → (θ₁ : Simplex X f g h₁)
      → h , θ == h₁ , θ₁
    comp-has-all-paths {x} {y} {z} {f} {g} θ θ₁ = contr-has-all-paths ⦃ base-fibrant fib ((tt , z) , tt , cst x) (tr X x y z) (source X g f)  ⦄ _ _
 
    comp : {x y : Obj X}
      → (c : Cnsₛ (Pb IdMnd (Ob X)) ((_ , y) , _ , cst x))
      → (ν : (p : Posₛ (Pb IdMnd (Ob X)) c) → Ob (Hom X) (Typₛ (Pb IdMnd (Ob X)) c p))
      → Arrow X x y
    comp c ν = fst $ contr-center (base-fibrant fib _ c ν)

    fill : {x y : Obj X}
      → (c : Cnsₛ (Pb IdMnd (Ob X)) ((_ , y) , _ , cst x))
      → (ν : (p : Posₛ (Pb IdMnd (Ob X)) c) → Ob (Hom X) (Typₛ (Pb IdMnd (Ob X)) c p))
      → _  -- Simplex X {!!} {!!} {!!}
    fill c ν = snd $ contr-center (base-fibrant fib _ c ν)
    
    id : (x : Obj X) → Arrow X x x
    id x = comp (lf (_ , x)) λ ()

    comp2 : {x y z : Obj X} (g : Arrow X y z) (f : Arrow X x y) → Arrow X x z
    comp2 {x} {y} {z} g f =
      fst $ contr-center (base-fibrant fib _ (tr X _ _ _) (source X g f))
      
    fill2 : {x y z : Obj X} (g : Arrow X y z) (f : Arrow X x y) → Simplex X f g (comp2 g f)
    fill2 {x} {y} {z} g f = snd $ contr-center (base-fibrant fib _ (tr X _ _ _) (source X g f))
    
    unit-l-cell₀ : {x y : Obj X} (f : Arrow X x y) → Ob (Hom (Hom X)) _
    unit-l-cell₀ {x} {y} f = fst $ contr-center (base-fibrant (hom-fibrant fib) _
      (nd _
          (λ { (inl tt) → lf (_ , y) , λ() ;
               (inr (tt , inl tt)) →  ηₛ (Pb IdMnd (Ob X)) ((_ , y) , _ , cst x) , _  ;
               (inr (tt , inr ())) })
          λ { (inl tt) → ηₛ N (_ , lf (_ , y) , λ ()) ;
              (inr (tt , inl tt)) → lf (_ , f) ;
              (inr (tt , inr (tt , ()))) })
              
      λ { (inl tt) → fill2 (id y) f  ;
          (inr (inl tt , inl tt)) → drp ;
          (inr (inl tt , inr (() , _))) ;
          (inr (inr (tt , inl tt) , ())) ;
          (inr (inr (tt , inr (tt , ())) , _)) })
        where drp = snd $ contr-center (base-fibrant fib _ (lf (_ , y)) λ ())

              N = Pb (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)) 

    unit-l-cell₁ : {x y : Obj X} (f : Arrow X x y)
      → Ob (Hom (Hom X))
          ((((tt , y) , tt , cst x) , f) ,
            ηₚ (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)) (((tt , y) , tt , cst x) , f)) 
    unit-l-cell₁ {x} {y} f = fst $ contr-center (base-fibrant (hom-fibrant fib) _ (lf (_ , f)) λ())

    unit-l2 : {x y : Obj X} (f : Arrow X x y) → comp2 (id y) f == f
    unit-l2 {x} {y} f =
      let contr = base-fibrant fib _ (ηₛ (Pb IdMnd (Ob X)) ((tt , y) , tt , cst x)) (cst f)
          p = pair= idp (λ= (η-pos-elimₛ (Pb IdMnd (Ob X)) ((tt , y) , tt , cst x) _ idp))
          unit-l-cell₀' = transport (λ z →
                            Ob (Hom (Hom (fst (fst C)))) ((((tt , y) , tt , cst x) , comp2 (id y) f) , z))
                            p (unit-l-cell₀ f)
      in fst= (contr-has-all-paths ⦃ contr ⦄
                (comp2 (id y) f , unit-l-cell₀') (f , unit-l-cell₁ f))


    unit-r2 : {x y : Obj X} (f : Arrow X x y) → comp2 f (id x) == f
    unit-r2 = {!!}

    assoc2 : {x y z t : Obj X}
      → (h : Arrow X z t) (g : Arrow X y z) (f : Arrow X x y)
      → comp2 (comp2 h g) f == comp2 h (comp2 g f)
    assoc2 h g f = {!!}

    record is-∞iso {x y : Obj X} (f : Arrow X x y) : Set where
      constructor mk-∞iso
      field
        g   : Arrow X y x
        f-g : comp2 f g == (id y) 
        g-f : comp2 g f == (id x) 

    ∞iso : (x y : Ob X tt) → Set 
    ∞iso x y = Σ (Arrow X x y) is-∞iso

    is-∞iso= : {x y : Obj X}
      → {f : Arrow X x y} 
      → {g g₁ : Arrow X y x}
      → (g=g₁ : g == g₁)
      → {f-g : comp2 f g == id y}
      → {f-g₁ : comp2 f g₁ == id y}
      → (f-g=f-g₁ : f-g == f-g₁ [ (λ g → comp2 f g == id y) ↓ g=g₁ ])
      → {g-f : comp2 g f == id x}
      → {g-f₁ : comp2 g₁ f == id x}
      → (g-f=g-f₁ : g-f == g-f₁ [ (λ g → comp2 g f == id x) ↓ g=g₁ ])
      → mk-∞iso g f-g g-f == mk-∞iso g₁ f-g₁ g-f₁
    is-∞iso= idp idp idp = idp

    is-∞iso-is-prop : {x y : Obj X} (f : Arrow X x y)
      → is-prop (is-∞iso f)
    is-∞iso-is-prop f = inhab-to-contr-is-prop {! !}

    ∞iso-is-set : (x y : Obj X) → is-set (∞iso x y)
    ∞iso-is-set x y = Σ-level (hom-sets _) λ _ → raise-level _ (is-∞iso-is-prop _)

    ∞iso= : {x y : Obj X}
      → {f g : ∞iso x y}
      → fst f == fst g
      → f == g
    ∞iso= p = pair= p (prop-has-all-paths-↓ ⦃ is-∞iso-is-prop _ ⦄ )

    id-is-∞iso : (x : Obj X) → is-∞iso (id x)
    is-∞iso.g (id-is-∞iso x) = id _
    is-∞iso.f-g (id-is-∞iso x) = unit-r2 _
    is-∞iso.g-f (id-is-∞iso x) = unit-r2 _

    id-to-∞iso : {x y : Obj X}
      → x == y
      → ∞iso x y
    id-to-∞iso {x} idp = id x , id-is-∞iso x 

    is-complete : Set
    is-complete = {x y : Obj X}
      → is-equiv (id-to-∞iso {x} {y})

    precat : PreCategory lzero lzero
    PreCategory.obj precat = Obj X
    PreCategory.hom precat x y = Arrow X x y
    PreCategory.comp precat = comp2
    PreCategory.assoc precat = assoc2
    PreCategory.id precat = id
    PreCategory.unit-l precat = unit-l2
    PreCategory.unit-r precat = unit-r2
    PreCategory.hom-sets precat x y = hom-sets ((tt , y) , tt , cst x)

    cat-∞cat-eq : {x y : Obj X} {f : Arrow X x y}
      → is-iso {P = precat} f ≃ is-∞iso f
    cat-∞cat-eq {x} {y} {f} = h , is-eq h i h-i i-h
      where h : is-iso {P = precat} f
                → is-∞iso f
            is-∞iso.g (h (mk-iso g f-g g-f)) = g
            is-∞iso.f-g (h (mk-iso g f-g g-f)) =
              f-g
            is-∞iso.g-f (h (mk-iso g f-g g-f)) =
              g-f

            i : is-∞iso f
                → is-iso {P = precat} f
            is-iso.g (i (mk-∞iso g f-g g-f)) = g
            is-iso.f-g (i (mk-∞iso g f-g g-f)) =
              f-g
            is-iso.g-f (i (mk-∞iso g f-g g-f)) =
              g-f

            i-h : i ∘ h ∼ idf _
            i-h e = is-iso= idp
              idp
              idp

            h-i : h ∘ i ∼ idf _
            h-i e = is-∞iso= idp
              idp
              idp
   
    module _ (cmpl : is-complete) where

      ∞iso-elim : {x : Obj X}
        → (P : {y : Obj X} → ∞iso x y → Set)
        → (d : P (id _ , id-is-∞iso _))
        → {y : Obj X}
        → (e : ∞iso x y)
        → P e
      ∞iso-elim {x} P d {y} e =
        let u = J (λ y p → P (–> (_ , cmpl) p)) d (<– (_ , cmpl) e)
        in transport P (<–-inv-r (_ , cmpl) e) u
      
  1-ucategory : Set (lsucc lzero)
  1-ucategory = Σ 1-category is-complete

  module _ (X : Category lzero lzero) where
    open Category X renaming (precat to C ; id to id' ; comp to comp-cat)

    mul : action (Slice ((Pb IdMnd (cst obj)))) λ { ((_ , x) , c , y) → hom (y tt) x }
    mul _ (lf i) δ = id' (snd i)
    mul _ (nd {i} c δ₁ ε) δ =
      comp-cat (δ (inl tt))  (mul _ (ε tt) λ p → δ (inr (tt , p)))

    is-assoc : {M : 𝕄} {A : Idx M → Set} (a : action M A) → Set
    is-assoc {M} {A} a = (i : Idx M) (σ : Cns M i)
      → (δ : (p : Pos M σ) → Cns M (Typ M σ p))
      → (ν : (p : Pos M (μ M σ δ)) → A (Typ M (μ M σ δ) p))
      → a i (μ M σ δ) ν == a i σ λ p → a _ (δ p) λ q → ν (μ-pos M σ δ p q)

    mul-γ : {i : Idx (Pb IdMnd (cst obj))} {c : Cns (Pb IdMnd (cst obj)) i}
      → (ρ : Cnsₛ (Pb IdMnd (cst obj)) (i , c))
      → (δ : (p : Pos (Pb IdMnd (cst obj)) {i} c)
             → Cns (Pb IdMnd (cst obj)) (Typ (Pb IdMnd (cst obj)) {i} c p))
      → (ε : (p : Pos (Pb IdMnd (cst obj)) {i} c)
             → Cnsₛ (Pb IdMnd (cst obj)) (Typ (Pb IdMnd (cst obj)) {i} c p , δ p))
      → (ν : (p : Pos (Slice ((Pb IdMnd (cst obj)))) (γ _ ρ δ ε)) →
               let ((_ , x) , _ , y) = Typ (Slice ((Pb IdMnd (cst obj)))) (γ _ ρ δ ε) p
               in hom (y tt) x)
      → mul _ (γ _ ρ δ ε) ν
        == comp-cat (mul _ ρ (ν ∘ (γ-pos-inl (Pb IdMnd (cst obj)) ρ δ ε)))
                    (mul _ (ε tt) (ν ∘ (γ-pos-inr _ ρ δ ε tt)))
    mul-γ {i} (lf _) δ ε ν =  ! (unit-l (mul _ (ε tt) ν))
    mul-γ {_ , _} (nd {i} c δ₁ ε₁) δ ε ν =
      let hyp = mul-γ (ε₁ tt) δ ε λ p → ν (inr (tt , p))
      in ap (λ x → comp-cat (ν (inl tt)) x) hyp ∙ (! (assoc _ _ _))
      
    mul-assoc : is-assoc {(Slice ((Pb IdMnd (cst obj))))} mul
    mul-assoc .(i , η (Pb IdMnd (λ _ → PreCategory.obj (Category.precat X))) i) (lf i) δ ν = idp
    mul-assoc .(i , μ (Pb IdMnd (λ _ → PreCategory.obj (Category.precat X))) {i} c δ₁) (nd {i} c δ₁ ε) δ ν =
      let hyp = mul-assoc _ (ε tt) (λ q → δ (inr (tt , q))) λ q → ν (γ-pos-inr _ (δ (inl tt)) δ₁ _ tt q)
          
      in mul-γ (δ true) δ₁ (λ p → μₛ _ (ε p) (λ q → δ (inr (p , q)))) ν
         ∙ ap (λ x →
                comp-cat (mul (i , c) (δ true)
                              (ν ∘ γ-pos-inl (Pb IdMnd (cst obj)) (δ true) δ₁
                              (λ p → μₛ _ (ε p) (λ q → δ (inr (p , q))))))
                          x)  
              hyp
  
    OC : OpetopicType.OpetopicType IdMnd
    Ob OC _ = obj
    Ob (Hom OC) ((_ , x) , _ , ν) = hom (ν tt) x
    Ob (Hom (Hom OC)) ((((_ , x) , _ , ν) , f) , pd , ν') = f == mul _ pd ν'
    Hom (Hom (Hom OC)) = Terminal _

    M = Slice (Pb (Slice (Pb IdMnd (Ob OC))) (Ob (Hom OC)))

    assoc-action : action M (Ob $ Hom $ Hom $ OC)
    assoc-action .(i , η (Pb (Slice (Pb IdMnd (Ob OC))) (Ob (Hom OC))) i) (lf i) κ = ! (unit-r (snd i))
    assoc-action .(_ , μ (Pb (Slice (Pb IdMnd (Ob OC))) (Ob (Hom OC)))
      {(((i , x) , (j , y)) , f)} (c , ν) δ)
      (nd {(((i , x) , (j , y)) , f)} (c , ν) δ ε) κ =
        let hyp p = assoc-action (_ , δ p) (ε p) λ q → κ (inr (p , q))
        in  κ (inl tt) ∙ ap (mul ((i , x) , j , y) c) (λ= hyp) ∙ ! (mul-assoc _ c (fst ∘ δ) _)

    OC-is-fibrant : is-fibrant (Hom OC)
    base-fibrant OC-is-fibrant f σ ν = pathto-is-contr (mul f σ ν)
    base-fibrant (hom-fibrant OC-is-fibrant) ((((tt , x) , _ , y) , f) , pd , κ) σ ν =
      inhab-prop-is-contr (assoc-action _ σ ν , tt) ⦃ Σ-level (has-level-apply (hom-sets _ _) _ _) λ _ → Unit-level ⦄
    hom-fibrant (hom-fibrant OC-is-fibrant) = Terminal-is-fibrant _

    OC-hom-sets : (i : Idxₛ (Pb IdMnd (Ob OC))) → is-set (Ob (Hom OC) i)
    OC-hom-sets ((tt , y) , tt , x) = hom-sets (x tt) y

    OC-cat : 1-category
    OC-cat = (OC , OC-is-fibrant) , OC-hom-sets

    id=id' : (x : obj) → id OC-cat x == id' x
    id=id' x = fst= (contr-path (base-fibrant OC-is-fibrant ((tt , x) , tt , cst x) (lf (_ , x)) λ ()) (id' x , idp))

    lem3 : {x y z : obj} (g : hom y z) (f : hom x y)
      → comp2 OC-cat g f , fill2 OC-cat g f 
        == (comp-cat g f) , ! (unit-r (comp-cat g f)) ∙ assoc _ _ _
    lem3 g f = contr-has-all-paths ⦃ pathto-is-contr (comp-cat g (comp-cat f (id' _))) ⦄ _ _

    comp2=comp-cat : {x y z : obj} (g : hom y z) (f : hom x y)
      → comp2 OC-cat g f == comp-cat g f
    comp2=comp-cat g f = fst= (lem3 g f)

    lem : (x : obj) → id OC-cat x == id' x
    lem x = ! (unit-l (id OC-cat x))
            ∙ ! (comp2=comp-cat (id' x) (id OC-cat x))
            ∙ unit-r2 OC-cat (id' x)
            
    to-from-cat : precat OC-cat == C
    to-from-cat =
      let obj= = idp
          hom= = idp
          id= = λ= lem
          comp= =
            let yo = λ= λ x → λ= λ y → λ= λ z →
                       λ= λ g → λ= λ f →
                         comp2=comp-cat {x} {y} {z} g f
            in ap (λ f → λ {x} {y} {z} → f x y z) yo
      in PreCategory=' obj= hom= comp= id= _ _ _ _ _ _ _ _

    cat-∞cat-eq' : {x y : obj} {f : hom x y}
      → is-iso {P = C} f ≃ is-∞iso OC-cat f
    cat-∞cat-eq' {x} {y} {f} = h , is-eq h i h-i i-h
      where h : is-iso f
                → is-∞iso OC-cat f
            is-∞iso.g (h (mk-iso g f-g g-f)) = g
            is-∞iso.f-g (h (mk-iso g f-g g-f)) =
              comp2=comp-cat _ _ ∙ f-g ∙ ! (id=id' y)
            is-∞iso.g-f (h (mk-iso g f-g g-f)) =
              comp2=comp-cat _ _ ∙ g-f ∙ ! (id=id' x)

            i : is-∞iso OC-cat f
                → is-iso f
            is-iso.g (i (mk-∞iso g f-g g-f)) = g
            is-iso.f-g (i (mk-∞iso g f-g g-f)) =
              ! (comp2=comp-cat _ _) ∙ f-g ∙ id=id' _
            is-iso.g-f (i (mk-∞iso g f-g g-f)) =
              ! (comp2=comp-cat _ _) ∙ g-f ∙ id=id' _

            i-h : i ∘ h ∼ idf _
            i-h e = is-iso= idp
              (prop-has-all-paths ⦃ has-level-apply (hom-sets _ _) _ _ ⦄ _ _)
              (prop-has-all-paths ⦃ has-level-apply (hom-sets _ _) _ _ ⦄ _ _)

            h-i : h ∘ i ∼ idf _
            h-i e = is-∞iso= OC-cat idp
              (prop-has-all-paths ⦃ has-level-apply (hom-sets _ _) _ _ ⦄ _ _)
              (prop-has-all-paths ⦃ has-level-apply (hom-sets _ _) _ _ ⦄ _ _)

    OC-is-complete : is-complete OC-cat
    OC-is-complete {x} {y} = transport! is-equiv (λ= aux) ((Σ-isemap-r λ _ → snd cat-∞cat-eq') ∘ise (univalent x y) )
      where aux : {x y : obj} (p : x == y)
                 → id-to-∞iso OC-cat p == let (f , iso) = id-to-iso p in (f , –> (cat-∞cat-eq') iso) 
            aux idp = ∞iso= OC-cat (id=id' _)



    UniCat : 1-ucategory
    UniCat = OC-cat , OC-is-complete
{-
  ODelta : ∞-ucategory
  ODelta = UniCat ThirdDef.Delta

  STypes : Set
  STypes = OpetopicTypeOver (IdMnd↓ Set) (fst $ fst $ ODelta)
-}
  module _ (C : 1-ucategory) where

    private 
      X = fst (fst (fst C))
      fib = snd (fst (fst C))
      hom-sets = snd (fst C)
      cmpl = snd C

      C-cat : 1-category
      C-cat = (X , fib) , hom-sets
 
    cat : Category lzero lzero
    Category.precat cat = precat C-cat
    Category.univalent cat x y =
      transport! is-equiv (λ= aux)
                 (Σ-isemap-r (λ _ → is-equiv-inverse (snd (cat-∞cat-eq C-cat)))
                 ∘ise cmpl)
      where aux : {x y : Obj X} (p : x == y)
                 → id-to-iso p == let (f , iso) = id-to-∞iso C-cat p in (f , <– (cat-∞cat-eq C-cat) iso) 
            aux idp = ≊= idp

 

    bar : (fst $ fst $ fst $ UniCat cat) ≃ₒ X [ id≃ₘ IdMnd ]
    _≃ₒ_[_].Ob≃ bar a = ide _
    fst (_≃ₒ_[_].Ob≃ (_≃ₒ_[_].Hom≃ bar) ((tt , y) , tt , x)) f = {!f!}
    is-equiv.g (snd (_≃ₒ_[_].Ob≃ (_≃ₒ_[_].Hom≃ bar) ((tt , y) , tt , x))) x₁ = {!!}
    is-equiv.f-g (snd (_≃ₒ_[_].Ob≃ (_≃ₒ_[_].Hom≃ bar) ((tt , y) , tt , x))) = {!!}
    is-equiv.g-f (snd (_≃ₒ_[_].Ob≃ (_≃ₒ_[_].Hom≃ bar) ((tt , y) , tt , x))) = {!!}
    is-equiv.adj (snd (_≃ₒ_[_].Ob≃ (_≃ₒ_[_].Hom≃ bar) ((tt , y) , tt , x))) = {!!}
    _≃ₒ_[_].Hom≃ (_≃ₒ_[_].Hom≃ bar) = {!!}
    
{-
    OpetopicType= : {M : 𝕄}
      → (X Y : OpetopicType M)
      → ?
      → x == y
    OpetopicType=
-}
