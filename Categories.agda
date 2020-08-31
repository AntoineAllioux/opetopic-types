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
open import Kan

module Categories where

  ∞-category : Set (lsucc lzero)
  ∞-category = Σ (OpetopicType IdMnd) (is-fibrant ∘ Hom)

  ∞-ucategory : Set (lsucc lzero)
  ∞-ucategory = Σ ∞-category (is-complete ∘ fst)

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

  module _ (X : Category lzero lzero) where
    open Category X renaming (precat to C)

    mul : action (Slice ((Pb IdMnd (cst obj)))) λ { ((_ , x) , c , y) → hom (y tt) x }
    mul _ (lf i) δ = id {snd i}
    mul _ (nd {i} c δ₁ ε) δ =
      δ (inl tt) ● mul _ (ε tt) λ p → δ (inr (tt , p))

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
        == (mul _ ρ (ν ∘ (γ-pos-inl (Pb IdMnd (cst obj)) ρ δ ε)))
            ● (mul _ (ε tt) (ν ∘ (γ-pos-inr _ ρ δ ε tt)))
    mul-γ {i} (lf _) δ ε ν =  ! (unit-l (mul _ (ε tt) ν))
    mul-γ {_ , _} (nd {i} c δ₁ ε₁) δ ε ν =
      let hyp = mul-γ (ε₁ tt) δ ε λ p → ν (inr (tt , p))
      in ap (λ x → ν (inl tt) ● x) hyp ∙ (! (assoc _ _ _))
      
    mul-assoc : is-assoc {(Slice ((Pb IdMnd (cst obj))))} mul
    mul-assoc .(i , η (Pb IdMnd (λ _ → PreCategory.obj (Category.precat X))) i) (lf i) δ ν = idp
    mul-assoc .(i , μ (Pb IdMnd (λ _ → PreCategory.obj (Category.precat X))) {i} c δ₁) (nd {i} c δ₁ ε) δ ν =
      let hyp = mul-assoc _ (ε tt) (λ q → δ (inr (tt , q))) λ q → ν (γ-pos-inr _ (δ (inl tt)) δ₁ _ tt q)
          
      in mul-γ (δ true) δ₁ (λ p → μₛ _ (ε p) (λ q → δ (inr (p , q)))) ν
         ∙ ap (λ x →
                mul (i , c) (δ true)
                    (ν ∘ γ-pos-inl (Pb IdMnd (cst obj)) (δ true) δ₁
                      (λ p → μₛ _ (ε p) (λ q → δ (inr (p , q)))))
                ● x)  
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
      inhab-prop-is-contr (assoc-action _ σ ν , tt) ⦃ Σ-level (has-level-apply (homs-sets _ _) _ _) λ _ → Unit-level ⦄
    hom-fibrant (hom-fibrant OC-is-fibrant) = Terminal-is-fibrant _

    OC-is-complete : is-complete OC
    OC-is-complete = {!!}

    UniCat : ∞-ucategory
    UniCat = (OC , OC-is-fibrant) , OC-is-complete

  ODelta : ∞-ucategory
  ODelta = UniCat ThirdDef.Delta

  STypes : Set
  STypes = OpetopicTypeOver (IdMnd↓ Set) (fst $ fst $ ODelta)

  module _ (C : ∞-ucategory) where

    X = fst $ fst C
    fib = snd $ fst C
    cmpl = snd C
      
    comp : {x y : Obj X}
      → (c : Cnsₛ (Pb IdMnd (Ob X)) ((_ , y) , _ , cst x))
      → (ν : (p : Posₛ (Pb IdMnd (Ob X)) c) → Ob (Hom X) (Typₛ (Pb IdMnd (Ob X)) c p))
      → Arrow X x y
    comp c ν = fst $ contr-center (base-fibrant fib _ c ν)

    fill : {x y : Obj X}
      → (c : Cnsₛ (Pb IdMnd (Ob X)) ((_ , y) , _ , cst x))
      → (ν : (p : Posₛ (Pb IdMnd (Ob X)) c) → Ob (Hom X) (Typₛ (Pb IdMnd (Ob X)) c p))
      → _ -- Simplex X {!!} {!!} {!!}
    fill c ν = snd $ contr-center (base-fibrant fib _ c ν)
    
    id : (x : Obj X) → Arrow X x x
    id x = comp (lf (_ , x)) λ ()

    comp2 : {x y z : Obj X} (g : Arrow X y z) (f : Arrow X x y) → Arrow X x z
    comp2 {x} {y} {z} g f =
      fst $ contr-center (base-fibrant fib _ (nd (_ , cst y) (cst (_ , cst x)) (cst (ηₛ (Pb IdMnd (Ob X)) (((_ , y) , _ , cst x)))) ) λ { (inl tt) → g ; (inr (tt , inl tt)) → f ; (inr (tt , inr ())) } )

    fill2 : {x y z : Obj X} (g : Arrow X y z) (f : Arrow X x y) → _ -- Simplex X f g (comp2 g f)
    fill2 {x} {y} {z} g f = snd $ contr-center (base-fibrant fib _ (nd (_ , cst y) (cst (_ , cst x)) (cst (ηₛ (Pb IdMnd (Ob X)) (((_ , y) , _ , cst x)))) ) λ { (inl tt) → g ; (inr (tt , inl tt)) → f ; (inr (tt , inr ())) } )
   

    unit-l-cell₀ : {x y : Obj X} (f : Arrow X x y) → _ -- Simplex X f (id y) f
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

    unit-l-cell₁ : {x y : Obj X} (f : Arrow X x y) → _
    unit-l-cell₁ {x} {y} f = fst $ contr-center (base-fibrant (hom-fibrant fib) _ (lf (_ , f)) λ())

    unit-l2 : {x y : Obj X} (f : Arrow X x y) → comp2 (id y) f == f
    unit-l2 {x} {y} f =
      let foo = base-fibrant fib _ (ηₛ _ ((_ , y) , _ , cst x)) 
         
          foo2 : let tr : Cnsₚ (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)) (_ , f)
                     tr = (nd (tt , cst y) (cst (tt , cst x))
                           (cst (ηₛ (Pb IdMnd (Ob X)) ((tt , y) , tt , cst x))))
                           , (λ { true → id y
                             ; (inr (tt , true)) → f
                             ; (inr (tt , inr ()))
                           })

                      ϕ : (p : Posₚ (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)) {i = _ , f} tr) → Cnsₚ (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)) (Typₚ (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)) {i = _ , f} tr p) 
                      ϕ = (λ { true → lf (tt , y) , (λ ())
                          ; (inr (tt , true))
                             → ηₛ (Pb IdMnd (Ob X)) ((tt , y) , tt , cst x) , (λ _ → f)
                            ; (inr (tt , inr ()))
                            })
                      
                 in μₚ (Slice (Pb IdMnd (Ob X))) (λ z → Ob (Hom X) z)
                   {i = ((tt , y) , tt , cst x) , f}
                   tr ϕ == ηₛ (Pb IdMnd (Ob X)) ((tt , y) , tt , cst x) , (λ _ → f)
          foo2 = pair= idp {!λ= (η-pos-elimₛ (Pb IdMnd (Ob X)) ? ? idp)!}


      in fst= (contr-has-all-paths ⦃ foo ⦄ (_ , {!unit-l-cell₀ f!}) (_ , unit-l-cell₁ f))


    unit-r2 : {x y : Obj X} (f : Arrow X x y) → comp2 f (id x) == f
    unit-r2 = {!!}

    assoc2 : {x y z t : Obj X}
      → (h : Arrow X z t) (g : Arrow X y z) (f : Arrow X x y)
      → comp2 (comp2 h g) f == comp2 h (comp2 g f)
    assoc2 h g f = {!!}

    is-equiv2 : {i : Idxₛ (Pb IdMnd (Ob X))} (f : Ob (Hom X) i) → Set
    is-equiv2 {((_ , y) , _ , x)} f =
      Σ (Arrow  X y (x tt)) λ g →
        (Ob (Hom (Hom X))
            ((((_ , x tt) , _ , x) , id (x tt)) ,
             nd (_ , cst y) (cst (_ , x)) (cst (ηₛ (Pb IdMnd (Ob X)) (((_ , y) , _ , x)))) ,
             λ { (inl tt) → g ; (inr (tt , inl tt)) → f ; (inr (tt , inr ())) }))
      × (Ob (Hom (Hom X))
            ((((_ , y) , _ , cst y) , id y) ,
              nd (_ , x) (cst (_ , cst y)) (cst (ηₛ (Pb IdMnd (Ob X)) (((_ , x tt) , _ , cst y)))) ,
              λ { (inl tt) → f ; (inr (tt , inl tt)) → g ; (inr (tt , inr ())) })) 

    equiv2 : (x y : Ob X tt) → Set 
    equiv2 x y = Σ (Arrow X x y) is-equiv2

    ua2 : {x y : Ob X tt} → x == y → equiv2 x y 
    ua2 {x} idp = id x , id x , {!!} , {!!}

    precat : PreCategory lzero lzero
    PreCategory.obj precat = Obj X
    PreCategory.hom precat x y = Ob (Hom X) ((tt , y) , tt , cst x)
    PreCategory._●_ precat = comp2
    PreCategory.assoc precat = assoc2
    PreCategory.id precat {x} = id x
    PreCategory.unit-l precat = unit-l2
    PreCategory.unit-r precat = unit-r2
    PreCategory.homs-sets precat = {!!}


    unival : (x y : Obj X) → is-equiv (id-to-iso {P = precat} x y)
    unival x y = is-eq (id-to-iso {P = precat} x y) g {!!} {!!}
      where g : _≊_ {P = precat} x y → x == y
            g (f , mk-cat-equiv g f-g g-f) =
              let e = base-complete cmpl tt tt (cst y) x y g (id y)
                  fill = transport (λ h → LiftFill (Ob X) (Ob (Hom X)) (Ob (Hom (Hom X))) tt tt (cst y) x y g h f) f-g {!fill2 f g!}
              in fst= (<– e (f , fill))
              
    cat : Category lzero lzero
    Category.precat cat = precat
    Category.univalent cat = unival

  Terminal-is-complete : (M : 𝕄) → is-complete (Terminal M)
  base-complete (Terminal-is-complete M) τ c ν y z p q = {!!}
  hom-complete (Terminal-is-complete M) = Terminal-is-complete _


  
