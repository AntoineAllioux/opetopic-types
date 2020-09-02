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
--open import Kan

module Categories where

  ∞-category : Set (lsucc lzero)
  ∞-category = Σ (OpetopicType IdMnd) (is-fibrant ∘ Hom)

  module _ (C : ∞-category) where

    private
      X = fst C
      fib = snd C

    foo : {x y z : Obj X}
      → {f : Arrow X x y} {g : Arrow X y z}
      → {h h₁ : Arrow X x z}
      → (θ : Simplex X f g h)
      → (θ₁ : Simplex X f g h₁)
      → h , θ == h₁ , θ₁
    foo {x} {y} {z} {f} {g} θ θ₁ = contr-has-all-paths ⦃ base-fibrant fib ((tt , z) , tt , cst x) (tr X x y z) (source X g f)  ⦄ _ _
 
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
      fst $ contr-center (base-fibrant fib _ (tr X _ _ _) (source X g f)) -- (nd (_ , cst y) (cst (_ , cst x)) (cst (ηₛ (Pb IdMnd (Ob X)) (((_ , y) , _ , cst x))))) λ { (inl tt) → g ; (inr (tt , inl tt)) → f ; (inr (tt , inr ())) } )

    fill2 : {x y z : Obj X} (g : Arrow X y z) (f : Arrow X x y) → Simplex X f g (comp2 g f)
    fill2 {x} {y} {z} g f = snd $ contr-center (base-fibrant fib _ (tr X _ _ _) (source X g f)) -- (nd (_ , cst y) (cst (_ , cst x)) (cst (ηₛ (Pb IdMnd (Ob X)) (((_ , y) , _ , cst x)))) ) λ { (inl tt) → g ; (inr (tt , inl tt)) → f ; (inr (tt , inr ())) } )
    
    degen₀ : {x y : Obj X} (f : Arrow X x y) → Simplex X (id x) f f
    degen₀ f = {!!}

    degen₁ : {x y : Obj X} (f : Arrow X x y) → Simplex X f (id y) f
    degen₁ f = {!!}

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
      let foo = base-fibrant fib _ (ηₛ _ ((_ , y) , _ , cst x)) {!!} 
         
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
                             → ηₛ (Pb IdMnd (Ob X)) ((tt , y) , tt , cst x) , (λ _ →  f )
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

    precat : PreCategory lzero lzero
    PreCategory.obj precat = Obj X
    PreCategory.hom precat x y = Arrow X x y
    PreCategory._●_ precat = comp2
    PreCategory.assoc precat = assoc2
    PreCategory.id precat {x} = id x
    PreCategory.unit-l precat = unit-l2
    PreCategory.unit-r precat = unit-r2
    PreCategory.homs-sets precat = {!!}

    record is-∞cat-equiv {x y : Obj X} (f : Arrow X x y) : Set where
      constructor mk-∞cat-equiv
      field
        g   : Arrow X y x
        f-g : Simplex X f g (id x) 
        g-f : Simplex X g f (id y) 

    ∞cat-equiv : (x y : Ob X tt) → Set 
    ∞cat-equiv x y = Σ (Arrow X x y) is-∞cat-equiv

    id-is-∞cat-equiv : (x : Obj X) → is-∞cat-equiv (id x)
    is-∞cat-equiv.g (id-is-∞cat-equiv x) = id _
    is-∞cat-equiv.f-g (id-is-∞cat-equiv x) = degen₀ (id _)
    is-∞cat-equiv.g-f (id-is-∞cat-equiv x) = degen₀ (id _)

    ∞cat-equiv-to-cat-equiv : {x y : Obj X} {f : Arrow X x y}
      → is-∞cat-equiv f
      → is-cat-equiv {P = precat} f
  {-  is-cat-equiv.g (∞cat-equiv-to-cat-equiv {x} {y} {f} (mk-∞cat-equiv g f-g g-f)) = g
    is-cat-equiv.f-g (∞cat-equiv-to-cat-equiv {x} {y} {f} (mk-∞cat-equiv g f-g g-f)) =
      fst= (foo (OC , OC-is-fibrant) (fill2 (OC , OC-is-fibrant) f g) g-f)
    is-cat-equiv.g-f (∞cat-equiv-to-cat-equiv {x} {y} {f} (mk-∞cat-equiv g f-g g-f)) =
      fst= (foo (OC , OC-is-fibrant) (fill2 (OC , OC-is-fibrant) g f) f-g)
-}

    
    is-complete : Set
    is-complete = {x y z : Obj X}
      → (f : ∞cat-equiv x y) (g : ∞cat-equiv x z)
      → ((y , fst f) == (z , fst g)) ≃ Σ (∞cat-equiv y z) λ h → Simplex X (fst f) (fst h) (fst g)

  ∞-ucategory : Set (lsucc lzero)
  ∞-ucategory = Σ ∞-category is-complete

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
    open Category X renaming (precat to C ; id to id')

    mul : action (Slice ((Pb IdMnd (cst obj)))) λ { ((_ , x) , c , y) → hom (y tt) x }
    mul _ (lf i) δ = id' {snd i}
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
    {-
    base-fibrant OC-is-fibrant .(i , η (Pb IdMnd (Ob OC)) i) (lf i) ν =
      has-level-in ((id' , idp) , λ _ → contr-has-all-paths ⦃ pathto-is-contr id' ⦄ _ _)
    base-fibrant OC-is-fibrant .(_ , μ (Pb IdMnd (Ob OC)) c δ) (nd c δ ε) ν =
      has-level-in (({!!} , {!!}) , {!!})
    --has-level-in ((({!ν true!} ● {!ν true!}) , {!!}) , {!!}) -- pathto-is-contr (mul f σ ν)
    base-fibrant (hom-fibrant OC-is-fibrant) ((((tt , x) , _ , y) , f) , pd , κ) σ ν =
      inhab-prop-is-contr (assoc-action _ σ ν , tt) ⦃ Σ-level (has-level-apply (homs-sets _ _) _ _) λ _ → Unit-level ⦄
    hom-fibrant (hom-fibrant OC-is-fibrant) = Terminal-is-fibrant _

    -}

    
    bar : C == precat (OC , OC-is-fibrant)
    bar = {!!}

    OC-is-complete : is-complete (OC , OC-is-fibrant)
    OC-is-complete {x} {y} {z} (f , p) (g , q) = h , is-eq h k {!!} {!!}
      where h : y , f == z , g
                → Σ (∞cat-equiv _ y z) (λ { (h , r) → Simplex OC f h g })
            h idp = (id (OC , OC-is-fibrant) y , id-is-∞cat-equiv _ y) , degen₁ (OC , OC-is-fibrant) f

            k : Σ (∞cat-equiv _ y z) (λ { (h , r) → Simplex OC f h g }) → y , f == z , g
            k ((h , r) , simpl) =
              let foo2 : _≊_ {P = precat (OC , OC-is-fibrant)} y z 
                  foo2 = (h , ∞cat-equiv-to-cat-equiv _ r) -- ∞cat-equiv-to-cat-equiv {f = h} r)
                  foo = is-equiv.g (univalent y z) {!foo2!} -- foo2
              in pair= {!!} {!!}

    UniCat : ∞-ucategory
    UniCat = (OC , OC-is-fibrant) , OC-is-complete

  ODelta : ∞-ucategory
  ODelta = UniCat ThirdDef.Delta

  STypes : Set
  STypes = OpetopicTypeOver (IdMnd↓ Set) (fst $ fst $ ODelta)

  module _ (C : ∞-ucategory) where

    private 
      X = fst $ fst C
      fib = snd $ fst C
      cmpl = snd C
      
    

    equiv-to-equiv : {x y : Obj X} {f : Arrow X x y}
      → is-cat-equiv {P = precat (X , fib)} f ≃ is-∞cat-equiv (X , fib) f
    equiv-to-equiv {f = f} = h , is-eq h k {!!} {!!}
      where h : is-cat-equiv {P = precat (X , fib)} f → is-∞cat-equiv (X , fib) f
            is-∞cat-equiv.g (h x) = is-cat-equiv.g x
            is-∞cat-equiv.f-g (h (mk-cat-equiv g f-g g-f)) =
              transport (λ x → Simplex X f g x) g-f (fill2 (X , fib) g f)
            is-∞cat-equiv.g-f (h (mk-cat-equiv g f-g g-f)) =
              transport (λ x → Simplex X g f x) f-g (fill2 (X , fib) f g)

            

            k : is-∞cat-equiv (X , fib) f → is-cat-equiv {P = precat (X , fib)} f
            is-cat-equiv.g (k x) = is-∞cat-equiv.g x
            is-cat-equiv.f-g (k x) = {!!}
            is-cat-equiv.g-f (k x) = {!!}
   

    unival : (x y : Obj X) → is-equiv (id-to-iso {P = precat (X , fib)} x y)
    unival x y = is-eq (id-to-iso {P = precat (X , fib)} x y) g h i
      where g : _≊_ {P = precat (X , fib)} x y → x == y
            g (f , mk-cat-equiv g f-g g-f) =
              let e = cmpl (_ , –> equiv-to-equiv (mk-cat-equiv g f-g g-f)) (id (X , fib) x , id-is-∞cat-equiv _ x)
                  g-is-equiv = –> equiv-to-equiv (cat-equiv-inv (mk-cat-equiv g f-g g-f))
                  
                  fill = transport (λ h → Simplex X f g h) g-f (fill2 (X , fib) g f)

                  foo : y , f == x , id (X , fib) x
                  foo = <– e ((g , g-is-equiv) , fill)
                   
              in ! (fst= (<– e ((g , g-is-equiv) , fill)))

            h : (e : x ≊ y) → id-to-iso x y (g e) == e
            h (f , mk-cat-equiv l f-g g-f) =
              let foo : fst (id-to-iso {P = precat (X , fib)} x y (g (f , mk-cat-equiv l f-g g-f))) == f
                  foo = {!idp!}
              in pair= {!!} {!!}

            i : (p : x == y) → g (id-to-iso x y p) == p
            i idp = {!idp!}
              
    cat : Category lzero lzero
    Category.precat cat = precat (X , fib)
    Category.univalent cat = unival

