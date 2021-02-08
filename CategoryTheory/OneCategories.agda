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
open import CategoryTheory.InftyCategories
--open import MonadEqv

module CategoryTheory.OneCategories where

  1-category : Set (lsucc lzero)
  1-category = Σ ∞-category λ { (X , fib) → (i : Idxₛ (Pb IdMnd (Ob X))) → is-set (Ob (Hom X) i) } 

  module _ (C : 1-category) where

    private
      X = fst (fst C)
      fib = snd (fst C)
      hom-sets = snd C            

    to-precategory : PreCategory lzero lzero
    PreCategory.obj to-precategory = Obj X
    PreCategory.hom to-precategory x y = Arrow X x y
    PreCategory.comp to-precategory = compₒ (X , fib) 
    PreCategory.assoc to-precategory = {! assocₒ ? !}
    PreCategory.id to-precategory = id (X , fib) 
    PreCategory.unit-l to-precategory = unit-lₒ (X , fib) 
    PreCategory.unit-r to-precategory = unit-rₒ (X , fib) 
    PreCategory.hom-sets to-precategory x y = hom-sets ((ttᵢ , y) , ttᵢ , cst x)

    is-isoₒ= : {x y : Obj X}
      → {f : Arrow X x y} 
      → {g g₁ : Arrow X y x}
      → (g=g₁ : g == g₁)
      → {f-g : compₒ (X , fib) f g == id (X , fib) y}
      → {f-g₁ : compₒ (X , fib)  f g₁ == id (X , fib)  y}
      → (f-g=f-g₁ : f-g == f-g₁ [ (λ g → compₒ (X , fib)  f g == id (X , fib)  y) ↓ g=g₁ ])
      → {g-f : compₒ (X , fib)  g f == id (X , fib)  x}
      → {g-f₁ : compₒ (X , fib)  g₁ f == id (X , fib)  x}
      → (g-f=g-f₁ : g-f == g-f₁ [ (λ g → compₒ (X , fib)  g f == id (X , fib) x) ↓ g=g₁ ])
      → mk-isoₒ {C = X , fib} g f-g g-f == mk-isoₒ g₁ f-g₁ g-f₁
    is-isoₒ= idp idp idp = idp

    is-isoₒ-is-prop : {x y : Obj X} (f : Arrow X x y)
      → is-prop (is-isoₒ (X , fib)  f)
    is-isoₒ-is-prop f = inhab-to-contr-is-prop {! !}

    isoₒ-is-set : (x y : Obj X) → is-set (isoₒ (X , fib) x y)
    isoₒ-is-set x y = Σ-level (hom-sets _) λ _ → raise-level _ (is-isoₒ-is-prop _)

    isoₒ= : {x y : Obj X}
      → {f g : isoₒ (X , fib)  x y}
      → fst f == fst g
      → f == g
    isoₒ= p = pair= p (prop-has-all-paths-↓ ⦃ is-isoₒ-is-prop _ ⦄ )

    iso-isoₒ-eq : {x y : Obj X} {f : Arrow X x y}
      → is-iso {P = to-precategory} f ≃ is-isoₒ (X , fib) f
    iso-isoₒ-eq {x} {y} {f} = h , is-eq h i h-i i-h
      where h : is-iso {P = to-precategory} f
                → is-isoₒ (X , fib)  f
            is-isoₒ.g (h (mk-iso g f-g g-f)) = g
            is-isoₒ.f-g (h (mk-iso g f-g g-f)) =
              f-g
            is-isoₒ.g-f (h (mk-iso g f-g g-f)) =
              g-f

            i : is-isoₒ (X , fib)  f
                → is-iso {P = to-precategory} f
            is-iso.g (i (mk-isoₒ g f-g g-f)) = g
            is-iso.f-g (i (mk-isoₒ g f-g g-f)) =
              f-g
            is-iso.g-f (i (mk-isoₒ g f-g g-f)) =
              g-f

            i-h : i ∘ h ∼ idf _
            i-h e = is-iso= idp
              idp
              idp

            h-i : h ∘ i ∼ idf _
            h-i e = is-isoₒ= idp
              idp
              idp

    to-category : (cmpl : is-complete (X , fib)) → Category lzero lzero
    Category.precat (to-category cmpl) = to-precategory
    Category.univalent (to-category cmpl) x y =
      transport! is-equiv (λ= aux)
                 (Σ-isemap-r (λ _ → is-equiv-inverse (snd iso-isoₒ-eq))
                 ∘ise cmpl)
      where aux : {x y : Obj X} (p : x == y)
                  → id-to-iso p == let (f , iso) = id-to-isoₒ (X , fib)  p in (f , <– iso-isoₒ-eq iso) 
            aux idp = ≊= idp
            
  1-ucategory : Set (lsucc lzero)
  1-ucategory = Σ ∞-ucategory λ { ((X , fib) , _) → (i : Idxₛ (Pb IdMnd (Ob X))) → is-set (Ob (Hom X) i) } 
{-
  module FromCategory (C : Category lzero lzero) where
    open Category C renaming (precat to P ; id to id')

    mul : action (Slice ((Pb IdMnd (cst obj)))) λ { ((_ , x) , c , y) → hom (y tt) x }
    mul _ (lf i) δ = id' (snd i)
    mul _ (nd {i} c δ₁ ε) δ =
      comp (δ (inl tt))  (mul _ (ε tt) λ p → δ (inr (ttᵢ , p)))

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
        == comp (mul _ ρ (ν ∘ (γ-pos-inl (Pb IdMnd (cst obj)) ρ δ ε)))
                    (mul _ (ε tt) (ν ∘ (γ-pos-inr _ ρ δ ε tt)))
    mul-γ {i} (lf _) δ ε ν =  ! (unit-l (mul _ (ε tt) ν))
    mul-γ {_ , _} (nd {i} c δ₁ ε₁) δ ε ν =
      let hyp = mul-γ (ε₁ tt) δ ε λ p → ν (inr (ttᵢ , p))
      in ap (λ x → comp (ν (inl tt)) x) hyp ∙ (! (assoc _ _ _))
      
    mul-assoc : is-assoc {(Slice ((Pb IdMnd (cst obj))))} mul
    mul-assoc .(i , η (Pb IdMnd (λ _ → PreCategory.obj (Category.precat C))) i) (lf i) δ ν = idp
    mul-assoc .(i , μ (Pb IdMnd (λ _ → PreCategory.obj (Category.precat C))) {i} c δ₁) (nd {i} c δ₁ ε) δ ν =
      let hyp = mul-assoc _ (ε tt) (λ q → δ (inr (ttᵢ , q))) λ q → ν (γ-pos-inr _ (δ (inl tt)) δ₁ _ tt q)
          
      in mul-γ (δ true) δ₁ (λ p → μₛ _ (ε p) (λ q → δ (inr (p , q)))) ν
         ∙ ap (λ x →
                comp (mul (i , c) (δ true)
                              (ν ∘ γ-pos-inl (Pb IdMnd (cst obj)) (δ true) δ₁
                              (λ p → μₛ _ (ε p) (λ q → δ (inr (p , q))))))
                          x)  
              hyp
  
    X : OpetopicType.OpetopicType IdMnd
    Ob X _ = obj
    Ob (Hom X) ((_ , x) , _ , ν) = hom (ν tt) x
    Ob (Hom (Hom X)) ((((_ , x) , _ , ν) , f) , pd , ν') = f == mul _ pd ν'
    Hom (Hom (Hom X)) = Terminal _

    M = Slice (Pb (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)))

    assoc-action : action M (Ob $ Hom $ Hom $ X)
    assoc-action .(i , η (Pb (Slice (Pb IdMnd (Ob X))) (Ob (Hom X))) i) (lf i) κ = ! (unit-r (snd i))
    assoc-action .(_ , μ (Pb (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)))
      {(((i , x) , (j , y)) , f)} (c , ν) δ)
      (nd {(((i , x) , (j , y)) , f)} (c , ν) δ ε) κ =
        let hyp p = assoc-action (_ , δ p) (ε p) λ q → κ (inr (p , q))
        in  κ (inl tt) ∙ ap (mul ((i , x) , j , y) c) (λ= hyp) ∙ ! (mul-assoc _ c (fst ∘ δ) _)

    X-is-fibrant : is-fibrant (Hom X)
    base-fibrant X-is-fibrant f σ ν = pathto-is-contr (mul f σ ν)
    base-fibrant (hom-fibrant X-is-fibrant) ((((ttᵢ , x) , _ , y) , f) , pd , κ) σ ν =
      inhab-prop-is-contr (assoc-action _ σ ν , tt) ⦃ Σ-level (has-level-apply (hom-sets _ _) _ _) λ _ → Unit-level ⦄
    hom-fibrant (hom-fibrant X-is-fibrant) = Terminal-is-fibrant _

    X-hom-sets : (i : Idxₛ (Pb IdMnd (Ob X))) → is-set (Ob (Hom X) i)
    X-hom-sets ((ttᵢ , y) , ttᵢ , x) = hom-sets (x tt) y

    X-cat : 1-category
    X-cat = (X , X-is-fibrant) , X-hom-sets

    id=id' : (x : obj) → id X-cat x == id' x
    id=id' x = fst= (contr-path (base-fibrant X-is-fibrant ((ttᵢ , x) , ttᵢ , cst x) (lf (_ , x)) λ ()) (id' x , idp))

    lem3 : {x y z : obj} (g : hom y z) (f : hom x y)
      → compₒ X-cat g f , fillₒ X-cat g f 
        == (comp g f) , ! (unit-r (comp g f)) ∙ assoc _ _ _
    lem3 g f = contr-has-all-paths ⦃ pathto-is-contr (comp g (comp f (id' _))) ⦄ _ _

    compₒ=comp : {x y z : obj} (g : hom y z) (f : hom x y)
      → compₒ X-cat g f == comp g f
    compₒ=comp g f = fst= (lem3 g f)

    lem : (x : obj) → id X-cat x == id' x
    lem x = ! (unit-l (id X-cat x))
            ∙ ! (compₒ=comp (id' x) (id X-cat x))
            ∙ unit-rₒ X-cat (id' x)
            
    to-from-cat : to-precategory X-cat == P
    to-from-cat =
      let obj= = idp
          hom= = idp
          id= = λ= lem
          comp= = {!!} {-
            let yo = λ= λ x → λ= λ y → λ= λ z →
                       λ= λ g → λ= λ f →
                         compₒ=comp {x} {y} {z} g f
            in ap (λ f → λ {x} {y} {z} → f x y z) yo -}
      in PreCategory=' obj= hom= comp= id= _ _ _ _ _ _ _ _

    iso-isoₒ-eq' : {x y : obj} {f : hom x y}
      → is-iso {P = P} f ≃ is-isoₒ X-cat f
    iso-isoₒ-eq' {x} {y} {f} = h , is-eq h i h-i i-h
      where h : is-iso f
                → is-isoₒ X-cat f
            is-isoₒ.g (h (mk-iso g f-g g-f)) = g
            is-isoₒ.f-g (h (mk-iso g f-g g-f)) =
              compₒ=comp _ _ ∙ f-g ∙ ! (id=id' y)
            is-isoₒ.g-f (h (mk-iso g f-g g-f)) =
              compₒ=comp _ _ ∙ g-f ∙ ! (id=id' x)

            i : is-isoₒ X-cat f
                → is-iso f
            is-iso.g (i (mk-isoₒ g f-g g-f)) = g
            is-iso.f-g (i (mk-isoₒ g f-g g-f)) =
              ! (compₒ=comp _ _) ∙ f-g ∙ id=id' _
            is-iso.g-f (i (mk-isoₒ g f-g g-f)) =
              ! (compₒ=comp _ _) ∙ g-f ∙ id=id' _

            i-h : i ∘ h ∼ idf _
            i-h e = is-iso= idp
              (prop-has-all-paths ⦃ has-level-apply (hom-sets _ _) _ _ ⦄ _ _)
              (prop-has-all-paths ⦃ has-level-apply (hom-sets _ _) _ _ ⦄ _ _)

            h-i : h ∘ i ∼ idf _
            h-i e = is-isoₒ= X-cat idp
              (prop-has-all-paths ⦃ has-level-apply (hom-sets _ _) _ _ ⦄ _ _)
              (prop-has-all-paths ⦃ has-level-apply (hom-sets _ _) _ _ ⦄ _ _)

    X-is-complete : is-complete X-cat
    X-is-complete {x} {y} = transport! is-equiv (λ= aux) ((Σ-isemap-r λ _ → snd iso-isoₒ-eq') ∘ise (univalent x y) )
      where aux : {x y : obj} (p : x == y)
                 → id-to-isoₒ X-cat p == let (f , iso) = id-to-iso p in (f , –> (iso-isoₒ-eq') iso) 
            aux idp = isoₒ= X-cat (id=id' _)
   
    to-1-ucategory : 1-ucategory
    to-1-ucategory = X-cat , X-is-complete

  fundamental-thm : {A : Set} {B : A → Set}
    → (p : is-contr (Σ A B))
    → (x : A) → B x ≃ (fst (contr-center p) == x)
  fundamental-thm {A} {B} p x = f , is-eq f g f-g g-f
    where f : B x → fst (contr-center p) == x
          f u = fst= (contr-path p (x , u))

          g : fst (contr-center p) == x → B x
          g q = transport B q (snd (contr-center p))

          f-g : f ∘ g ∼ idf _
          f-g idp = ap fst= (contr-has-all-paths ⦃ =-preserves-level p ⦄ _ _)

          g-f : g ∘ f ∼ idf _
          g-f u = to-transp (snd= (contr-path p (x , u)))

  record has-levelₒ {M : 𝕄} (n : ℕ₋₂) (X : OpetopicType M) : Set where
    coinductive
    field
      base-level : (i : Idx M) → has-level n (Ob X i)
      hom-level : has-levelₒ n (Hom X)
  open has-levelₒ


  unique-action-level : (M : 𝕄) (A : Idx M → Set) (W : Idx (Slice (Pb M A)) → Set)
     → (act : unique-action M A W)
     → {n : ℕ₋₂} (p : (i : Idx M) → has-level (S n) (A i))
     → (i : Idx (Slice (Pb M A)))
     → has-level n (W i)
  unique-action-level M₁ A W act p ((i , x) , c  , ν) =
     equiv-preserves-level ((fundamental-thm {A i} {λ x → W ((i , x) , c  , ν)} (act i c ν) x) ⁻¹)
                           ⦃ has-level-apply (p i) _ _ ⦄

  fibrant-opetopic-type-level : {M : 𝕄}
    → (X : OpetopicType M)
    → (fib : is-fibrant X)
    → (n : ℕ₋₂)
    → ((i : Idx M) → has-level n (Ob X i))
    → has-levelₒ n X
  base-level (fibrant-opetopic-type-level X fib n p) = p
  hom-level (fibrant-opetopic-type-level {M} X fib n p) =
    fibrant-opetopic-type-level (Hom X) (hom-fibrant fib) n
         (unique-action-level M (Ob X) (Ob (Hom X)) (base-fibrant fib) λ i → raise-level _ (p i))
                                                                              
  contr-types-are-equiv : ∀ {l} {A B : Set l}
    → is-contr A
    → is-contr B
    → A ≃ B
  contr-types-are-equiv cA cB = (λ _ → contr-center cB) , contr-to-contr-is-equiv _ cA cB

  {-# TERMINATING #-}
  contr-opetopic-types-are-equiv : {M N : 𝕄}
    → (e : M ≃ₘ N)
    → (X : OpetopicType M)
    → (Y : OpetopicType N)
    → has-levelₒ ⟨-2⟩ X
    → has-levelₒ ⟨-2⟩ Y
    → X ≃ₒ Y [ e ]
  _≃ₒ_[_].Ob≃ (contr-opetopic-types-are-equiv e X Y cX cY) i = contr-types-are-equiv (base-level cX i) (base-level cY _)
  _≃ₒ_[_].Hom≃ (contr-opetopic-types-are-equiv e X Y cX cY) = contr-opetopic-types-are-equiv {!Slice≃ ?!} (Hom X) (Hom Y) (hom-level cX) (hom-level cY)

  postulate
    C : 1-ucategory

  X : OpetopicType IdMnd
  X = fst (fst (fst C))
  X-fib = snd $ fst $ fst C
  X-hom-sets = snd $ fst C

  D = to-category (fst C) (snd C)
  
  C' = FromCategory.to-1-ucategory D
  Y = fst $ fst $ fst C'
  Y-fib = snd $ fst $ fst C'
  Y-hom-sets = snd $ fst C'
  
  comp'=mul : {x y : Obj X}
    → (c : Cnsₛ (Pb IdMnd (Ob X)) ((_ , y) , _ , cst x))
    → (ν : (p : Posₛ (Pb IdMnd (Ob X)) c) → Ob (Hom X) (Typₛ (Pb IdMnd (Ob X)) c p))
    → comp-dec (fst C) c ν == FromCategory.mul D _ c ν
  comp'=mul c ν = {!!}
 
  to-from-opetopic-types : (fst $ fst $ fst $ FromCategory.to-1-ucategory D) ≃ₒ X [ id≃ₘ IdMnd ]
  _≃ₒ_[_].Ob≃ to-from-opetopic-types _ = ide _
  _≃ₒ_[_].Ob≃ (_≃ₒ_[_].Hom≃ to-from-opetopic-types) =
    let p : Slice≃ (Pb≃ (id≃ₘ IdMnd) {X = Ob X} λ i → ide (Ob X i)) == id≃ₘ (Slice (Pb IdMnd (Ob X)))
        p = {! ap (Slice≃ {Pb IdMnd (Ob X)} {Pb IdMnd (Ob X)}) (Pb≃-id IdMnd (Ob X)) !} ∙ Slice≃-id (Pb IdMnd (Ob X))  

    in transport (λ e → Ob (Hom X) ≃[ e ] Ob (Hom X)) (! (ap Idx≃ p)) λ _ → ide _
  _≃ₒ_[_].Ob≃ (_≃ₒ_[_].Hom≃ (_≃ₒ_[_].Hom≃ to-from-opetopic-types)) ((((i , x) , c , ν) , f) , pd , κ) =
    let --e : Ob (Hom (Hom (fst $ fst $ fst $ FromCategory.to-1-ucategory D)))
        --       ((((i , x) , c , ν) , f) , pd , κ)
        --    ≃ Ob (Hom (Hom X)) (–> (Idx≃ (Slice≃ (Pb≃ (Slice≃ (Pb≃ (id≃ₘ IdMnd) (λ _ → ide _))) {!λ _ → ? !} ))) ((((i , x) , c , ν) , f) , pd , κ))
        e = {!!}

        
        
    in e -- (λ { idp → {!!} }) , {!!}
    where e' : Ob (Hom (Hom (fst $ fst $ fst $ FromCategory.to-1-ucategory D)))
               ((((i , x) , c , ν) , f) , pd , κ)
            ≃ Ob (Hom (Hom X)) (–> (Idx≃ (id≃ₘ (Slice (Pb (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)))))) ((((i , x) , c , ν) , f) , pd , κ))
          e' = g , is-eq g h g-h h-g
            where g : Ob (Hom (Hom (fst $ fst $ fst $ FromCategory.to-1-ucategory D))) ((((i , x) , c , ν) , f) , pd , κ)
                      → Ob (Hom (Hom X)) (–> (ide (Idxₛ (Pb (Slice (Pb IdMnd (Ob X))) (Ob (Hom X))))) ((((i , x) , c , ν) , f) , pd , κ))
                  g idp =
                    let r : Ob (Hom (Hom X)) ((((i , x) , c , ν) , comp-dec (fst C) pd κ) , pd , κ)
                        r = fill-dec (fst C) pd κ

                        s : Ob (Hom (Hom X)) ((((i , x) , c , ν) , FromCategory.mul D _ pd κ) , pd , κ)
                        s = transport (λ u → Ob (Hom (Hom X)) ((((i , x) , c , ν) , u) , pd , κ)) (comp'=mul pd κ) r
                    in s

                  h : Ob (Hom (Hom X)) (–> (ide (Idxₛ (Pb (Slice (Pb IdMnd (Ob X))) (Ob (Hom X))))) ((((i , x) , c , ν) , f) , pd , κ))
                      → Ob (Hom (Hom (fst $ fst $ fst $ FromCategory.to-1-ucategory D))) ((((i , x) , c , ν) , f) , pd , κ)
                  h x =
                    let p : f == FromCategory.mul D ((i , _) , c , ν) pd κ
                        p = {!!}

                        q : {!!} == {!!}
                        q = {!x!}
                    in p

                  g-h : g ∘ h ∼ idf _
                  g-h _ =
                    let x = unique-action-level
                              (Slice (Pb IdMnd (Ob X)))
                              (Ob (Hom X))
                              (Ob (Hom (Hom X)))
                              (base-fibrant X-fib)
                              X-hom-sets _
                    in prop-has-all-paths ⦃ x ⦄ _ _

                  h-g : h ∘ g ∼ idf _
                  h-g x =
                    let x = unique-action-level
                              (Slice (Pb IdMnd (Ob Y)))
                              (Ob (Hom Y))
                              (Ob (Hom (Hom Y)))
                              (base-fibrant Y-fib)
                              Y-hom-sets
                              ((((i , _) , c , ν) , f) , pd , κ)
                    in prop-has-all-paths ⦃ x ⦄ _ _

  _≃ₒ_[_].Hom≃ (_≃ₒ_[_].Hom≃ (_≃ₒ_[_].Hom≃ to-from-opetopic-types)) =
    contr-opetopic-types-are-equiv _ _ _  (fibrant-opetopic-type-level _ (Terminal-is-fibrant _) _ λ _ → Unit-level)
                (fibrant-opetopic-type-level _ (hom-fibrant $ hom-fibrant $ X-fib) _
                        (unique-action-level (Slice (Pb (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)))) (Ob (Hom (Hom X))) (Ob (Hom (Hom (Hom X)))) (base-fibrant $ hom-fibrant $ X-fib) (unique-action-level (Slice (Pb IdMnd (Ob X))) (Ob (Hom X)) (Ob (Hom (Hom X))) (base-fibrant X-fib) λ _ → X-hom-sets _)))
-}
