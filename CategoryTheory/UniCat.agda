{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import HoTT
open import lib.NType2
open import lib.Equivalence2

module CategoryTheory.UniCat where

  _|>_ : ∀ {i j} {A : Set i} {B : A → Set j} → (x : A) → Π A B → B x
  x |> f = f x

  infixl 10 _|>_

  -- Definition of a pre-category
  record PreCategory lobj larrow : Set (lsucc (lmax lobj larrow)) where
    field
      obj       : Set lobj
      hom       : obj → obj → Set larrow
      comp       : {x y z : obj} (g : hom y z) (f : hom x y) → hom x z
      assoc     : {x y z t : obj} (h : hom z t) (g : hom y z) (f : hom x y) → comp (comp h g) f == comp h (comp g f)
      id        : (x : obj) → hom x x
      unit-l    : {x y : obj} (f : hom x y) → comp (id y) f == f
      unit-r    : {x y : obj} (f : hom x y) → comp f (id x) == f
      hom-sets : (x y : obj) → is-set (hom x y)

  PreCategory= : ∀ {lobj larrow}
    → {obj obj₁ : Set lobj}
    → (obj= : obj == obj₁)
    → {hom : obj → obj → Set larrow}
    → {hom₁ : obj₁ → obj₁ → Set larrow}
    → (hom= : hom == hom₁ [ (λ obj → obj → obj → Set larrow) ↓ obj= ])
    → {comp : {x y z : obj} (g : hom y z) (f : hom x y) → hom x z}
    → {comp₁ : {x y z : obj₁} (g : hom₁ y z) (f : hom₁ x y) → hom₁ x z}
    → (comp= : comp == comp₁ [ (λ { (obj , hom) →  {x y z : obj} (g : hom y z) (f : hom x y) → hom x z}) ↓ pair= obj= hom= ])
    → {id : (x : obj) → hom x x}
    → {id₁ : (x : obj₁) → hom₁ x x}
    → (id= : id == id₁ [ (λ { (obj , hom) → (x : obj) → hom x x}) ↓ pair= obj= hom= ])
    → {assoc : {x y z t : obj} (h : hom z t) (g : hom y z) (f : hom x y) → comp (comp h g) f == comp h (comp g f)}
    → {assoc₁ : {x y z t : obj₁} (h : hom₁ z t) (g : hom₁ y z) (f : hom₁ x y) → comp₁ (comp₁ h g) f == comp₁ h (comp₁ g f)}
    → (assoc= : assoc == assoc₁ [ (λ { (obj , hom , comp) → {x y z t : obj} (h : hom z t) (g : hom y z) (f : hom x y) → comp (comp h g) f == comp h (comp g f) }) ↓ pair= obj= (↓-Σ-in hom= comp=) ])
    → {unit-l : {x y : obj} (f : hom x y) → comp (id y) f == f}
    → {unit-l₁ : {x y : obj₁} (f : hom₁ x y) → comp₁ (id₁ y) f == f}
    → (unit-l= : unit-l == unit-l₁ [ (λ { (obj , hom , id , comp) → {x y : obj} (f : hom x y) → comp (id y) f == f }) ↓ pair= obj= (↓-Σ-in hom= (↓-×-in id= comp=)) ])
    → {unit-r : {x y : obj} (f : hom x y) → comp f (id x) == f}
    → {unit-r₁ : {x y : obj₁} (f : hom₁ x y) → comp₁ f (id₁ x) == f}
    → (unit-r= : unit-r == unit-r₁ [ (λ { (obj , hom , id , comp) → {x y : obj} (f : hom x y) → comp f (id x) == f })  ↓ pair= obj= (↓-Σ-in hom= (↓-×-in id= comp=)) ])
    → {hom-sets : (x y : obj) → is-set (hom x y)}
    → {hom-sets₁ : (x y : obj₁) → is-set (hom₁ x y)}
    → (hom-sets= : hom-sets == hom-sets₁ [ (λ { (obj , hom) → (x y : obj) → is-set (hom x y) }) ↓ pair= obj= hom= ])
    → record { obj = obj ; hom = hom ; comp = comp ; id = id ; assoc = assoc ; unit-l = unit-l ; unit-r = unit-r ; hom-sets = hom-sets }
      == record { obj = obj₁ ; hom = hom₁ ; comp = comp₁ ; id = id₁ ; assoc = assoc₁ ; unit-l = unit-l₁ ; unit-r = unit-r₁ ; hom-sets = hom-sets₁ }
  PreCategory= idp idp idp idp idp idp idp idp = idp

  PreCategory=' : ∀ {lobj larrow}
    → {obj obj₁ : Set lobj}
    → (obj= : obj == obj₁)
    → {hom : obj → obj → Set larrow}
    → {hom₁ : obj₁ → obj₁ → Set larrow}
    → (hom= : hom == hom₁ [ (λ obj → obj → obj → Set larrow) ↓ obj= ])
    → {comp : {x y z : obj} (g : hom y z) (f : hom x y) → hom x z}
    → {comp₁ : {x y z : obj₁} (g : hom₁ y z) (f : hom₁ x y) → hom₁ x z}
    → (comp= : comp == comp₁ [ (λ { (obj , hom) →  {x y z : obj} (g : hom y z) (f : hom x y) → hom x z}) ↓ pair= obj= hom= ])
    → {id : (x : obj) → hom x x}
    → {id₁ : (x : obj₁) → hom₁ x x}
    → (id= : id == id₁ [ (λ { (obj , hom) → (x : obj) → hom x x}) ↓ pair= obj= hom= ])
    → (assoc : {x y z t : obj} (h : hom z t) (g : hom y z) (f : hom x y) → comp (comp h g) f == comp h (comp g f))
    → (assoc₁ : {x y z t : obj₁} (h : hom₁ z t) (g : hom₁ y z) (f : hom₁ x y) → comp₁ (comp₁ h g) f == comp₁ h (comp₁ g f))
    → (unit-l : {x y : obj} (f : hom x y) → comp (id y) f == f)
    → (unit-l₁ : {x y : obj₁} (f : hom₁ x y) → comp₁ (id₁ y) f == f)
    → (unit-r : {x y : obj} (f : hom x y) → comp f (id x) == f)
    → (unit-r₁ : {x y : obj₁} (f : hom₁ x y) → comp₁ f (id₁ x) == f)
    → (hom-sets : (x y : obj) → is-set (hom x y))
    → (hom-sets₁ : (x y : obj₁) → is-set (hom₁ x y))
    → record { obj = obj ; hom = hom ; comp = comp ; id = id ; assoc = assoc ; unit-l = unit-l ; unit-r = unit-r ; hom-sets = hom-sets }
      == record { obj = obj₁ ; hom = hom₁ ; comp = comp₁ ; id = id₁ ; assoc = assoc₁ ; unit-l = unit-l₁ ; unit-r = unit-r₁ ; hom-sets = hom-sets₁ }
  PreCategory=' obj= hom= comp= id= assoc assoc₁ unit-l unit-l₁ unit-r unit-r₁ hom-sets hom-sets₁ =
    let assoc= = prop-has-all-paths-↓ ⦃ {!!} ⦄
        unit-r= = prop-has-all-paths-↓ ⦃ {!!} ⦄
        unit-l= = prop-has-all-paths-↓ ⦃ {!!} ⦄
        homs-sets= = prop-has-all-paths-↓ ⦃ {!!} ⦄
    in PreCategory= obj= hom= comp= id= assoc= unit-l= unit-r= homs-sets=


  module _ {lobj larrow} {P : PreCategory lobj larrow} where
  
    open PreCategory P

    -- Definition of an equivalence in a category
    record is-iso {x y : obj} (f : hom x y) : Set larrow where
      constructor mk-iso
      field
        g : hom y x
        f-g : comp f g == id y
        g-f : comp g f == id x
    open is-iso

    is-iso= : {x y : obj} {f : hom x y}
      → {g₀ g₁ : hom y x}
      → (g₀=g₁ : g₀ == g₁)
      → {f-g₀ : comp f g₀ == id y}
      → {f-g₁ : comp f g₁ == id y}
      → (f-g₀=f-g₁ : f-g₀ == f-g₁ [ (λ g → comp f g == id y) ↓ g₀=g₁ ])
      → {g-f₀ : comp g₀ f == id x}
      → {g-f₁ : comp g₁ f == id x}
      → (g-f₀=g-f₁ : g-f₀ == g-f₁ [ (λ g → comp g f == id x) ↓ g₀=g₁ ])
      → mk-iso g₀ f-g₀ g-f₀ == mk-iso g₁ f-g₁ g-f₁
    is-iso= idp idp idp = idp

    _≊_ : (x y : obj) → Set larrow
    _≊_ x y = Σ (hom x y) (λ f → is-iso f)

    id-is-iso : (x : obj) → is-iso (id x)
    id-is-iso x = mk-iso (id _) (unit-l _) (unit-l _)

    —> : {x y : obj} (e : x ≊ y) → hom x y
    —> = fst

    <— : {x y : obj} (e : x ≊ y) → hom y x
    <— e = is-iso.g (snd e)

    <—-inv-l : {x y : obj} (e : x ≊ y)
      → comp (<— e) (—> e) == id x
    <—-inv-l e = is-iso.g-f (snd e)

    <—-inv-r : {x y : obj} (e : x ≊ y)
      → comp (—> e) (<— e) == id y
    <—-inv-r e = is-iso.f-g (snd e) 

    id-to-iso : (x y : obj) → x == y → x ≊ y
    id-to-iso x _ idp = _ , id-is-iso x

    iso-inv : {x y : obj}
      → {f : hom x y}
      → (p : is-iso f)
      → is-iso (is-iso.g p)
    is-iso.g (iso-inv {f = f} p) = f
    is-iso.f-g (iso-inv p) = is-iso.g-f p
    is-iso.g-f (iso-inv p) = is-iso.f-g p

    is-monic : {x y : obj} (f : hom x y) → Set (lmax lobj larrow)
    is-monic {x} {y} f = {z : obj} (g h : hom z x)
      → comp f g == comp f h
      → g == h

    is-epic : {x y : obj} (f : hom x y) → Set (lmax lobj larrow)
    is-epic {x} {y} f = {z : obj} (g h : hom y z)
      → comp g f == comp h f
      → g == h

    iso-is-monic : {x y : obj} {f : hom x y}
      → is-iso f
      → is-monic f
    iso-is-monic f-iso g h p = ap (λ x → comp (is-iso.g f-iso) x) p
      |> transport! (λ { (l , r) → l == r}) (pair×= (assoc _ _ _) (assoc _ _ _))
      |> transport (λ f → comp f g == comp f h) (is-iso.g-f f-iso)
      |> transport (λ { (l , r) → l == r }) (pair×= (unit-l _) (unit-l _))

    iso-is-epic : {x y : obj} {f : hom x y}
      → is-iso f
      → is-epic f
    iso-is-epic f-iso g h p = {!!}

    is-iso-is-prop : {x y : obj} (f : hom x y)
      → is-prop (is-iso f)
    is-iso-is-prop f =
      let is-iso-has-all-paths : (g h : is-iso f) → g == h
          is-iso-has-all-paths g h = is-iso= (iso-is-monic g (is-iso.g g) (is-iso.g h) (is-iso.f-g g ∙ ! (is-iso.f-g h)))
            (prop-has-all-paths-↓ ⦃ has-level-apply (hom-sets _ _) _ _  ⦄)
            (prop-has-all-paths-↓ ⦃ has-level-apply (hom-sets _ _) _ _  ⦄)
      in inhab-to-contr-is-prop λ g → has-level-in (g , is-iso-has-all-paths _)

    ≊-is-set : (x y : obj) → is-set (x ≊ y)
    ≊-is-set x y = Σ-level (hom-sets _ _) λ _ → raise-level _ (is-iso-is-prop _)

    ≊= : {x y : obj}
      → {f g : x ≊ y}
      → fst f == fst g
      → f == g
    ≊= p = pair= p (prop-has-all-paths-↓ ⦃ is-iso-is-prop _ ⦄)

  open PreCategory

  is-univalent-category : ∀ {lobj larrow}
    → PreCategory lobj larrow
    → Set (lmax lobj larrow)
  is-univalent-category X = (x y : obj X) → is-equiv (id-to-iso {P = X} x y)

  record Category lobj larrow : Set (lsucc (lmax lobj larrow)) where
    field
      precat    : PreCategory lobj larrow
      univalent : is-univalent-category precat
    open PreCategory precat public

  is-univalent-category-is-prop : ∀ {lobj larrow}
    → (X : PreCategory lobj larrow)
    → is-prop (is-univalent-category X)
  is-univalent-category-is-prop X =
    Π-level λ _ → Π-level λ _ → is-equiv-is-prop

  Category= : ∀ {lobj larrow} {C C' : PreCategory lobj larrow} 
    → (p : C == C')
    → {uc : is-univalent-category C}
    → {uc' : is-univalent-category C'}
    → uc == uc' [ is-univalent-category  ↓ p  ]
    → record { precat = C ; univalent = uc } == record { precat = C' ; univalent = uc' }
  Category= idp idp = idp
    
  open Category

  module _ {l l'} (X : Category l l') where
    open Category X renaming (precat to C)

    ≊-elim : ∀ {l} {x : obj C}
      → (P : {y : obj C} → _≊_ {P = C} x y → Set l)
      → (d : P (_ , id-is-iso x))
      → {y : obj C} (i : x ≊ y) → P i
    ≊-elim {x = x} P d {y} i =
      let u = J (λ y p → P {y} (id-to-iso _ _ p)) d (is-equiv.g (univalent X _ _) i)
      in transport P (is-equiv.f-g (univalent X _ _) i) u

    pathto-idp : ∀ {l} {A : Set l}
      → {x y : A} (p : x == y)
      → p == idp [ (λ x → x == y) ↓ p ]
    pathto-idp idp = idp

    ≊-elim-β : ∀ {l} {x : obj C}
      → (P : {y : obj C} → _≊_ {P = C} x y → Set l)
      → (d : P (_ , id-is-iso x))
      → ≊-elim P d (_ , id-is-iso x) == d
    ≊-elim-β {x = x} P d =
      let u = J (λ y p → P {y} (id-to-iso _ _ p)) d (<– (_ , univalent X _ _) (_ , id-is-iso _))

          p = ap (–> (_ , univalent X _ _)) (<–-inv-l (_ , univalent X _ _) idp)

          u=d : u == d [ P ↓ p ]
          u=d = apd (J (λ y p → P {y} (id-to-iso _ _ p)) d) (<–-inv-l (_ , univalent X _ _) idp)
                |> ↓-ap-in P (–> (_ , univalent X _ _))

          <–-inv-r=idp : <–-inv-r (_ , univalent X _ _) (_ , id-is-iso _) == idp
                          [ (λ x → x == _) ↓ p ]
          <–-inv-r=idp = pathto-idp p
                         |> transport (λ x → x == idp [ (λ x → x == _) ↓ p ])
                                      (<–-inv-adj (_ , univalent X x x) idp)
          
      in transport! (λ { (_ , x , y) → transport P y x == d})
                    (pair= _ (↓-×-in u=d <–-inv-r=idp))
                    idp
      
    transport-iso-lem : {x y z : obj C} (f : hom C x y) (i : _≊_ {P = C} y z)
      → transport (hom C x) (<– (_ , univalent X y z) i) f
        == (comp C (fst i) f)
    transport-iso-lem {x} {y} {z} f =
      let foo = transport (λ p → transport (hom C x) p f == comp C (id C y) f) (! (<–-inv-l (_ , univalent X y y) idp)) (! (unit-l C f))
      in ≊-elim (λ {z} i → transport (hom C x) (<– (_ , univalent X y z) i) f == comp C (fst i) f) foo

    transport-iso-lem-id : {x y : obj C} (f : hom C x y)
      → transport-iso-lem f (_ , id-is-iso _) == ! (unit-l C f) [ (λ p → transport (hom C x) p f == comp C (id C y) f) ↓ <–-inv-l (_ , univalent X _ _) idp ]
    transport-iso-lem-id {x} {y} f =
      let p = transport (λ p → transport (hom C x) p f == comp C (id C y) f) (! (<–-inv-l (_ , univalent X y y) idp)) (! (unit-l C f))
      
          q : p == ! (unit-l C f) [ (λ p → transport (hom C x) p f == comp C (id C y) f) ↓ <–-inv-l (_ , univalent X _ _) idp  ]
          q = transp-↓ (λ p → transport (hom C x) p f == comp C (id C y) f) (<–-inv-l (_ , univalent X _ _) idp) (! (unit-l C f))
          
      in ≊-elim-β (λ {z} i → transport (hom C x) (<– (_ , univalent X y z) i) f == comp C (fst i) f) p ∙ᵈ q  


  module _ {lobj lobj' larrow larrow'} (Cat : Category lobj larrow) (Cat' : Category lobj' larrow') where

    open Category Cat renaming (precat to C)
    open Category Cat' renaming (precat to C')   

    record Functor : Set (lsucc (lmax (lmax lobj lobj') (lmax larrow larrow'))) where
      field
        fobj  : obj C → obj C'
        farr  : {x y : obj C} → hom C x y → hom C' (fobj x) (fobj y)
        fcomp : {x y z : obj C} (f : hom C x y) (g : hom C y z) → farr (comp C g f) == comp C' (farr g) (farr f) 
        fid   : (x : obj C) → farr (id C x) == id C' (fobj x)

    open Functor public

    record NatTrans (F F' : Functor) : Set (lsucc (lmax (lmax lobj lobj') (lmax larrow larrow'))) where
      field
        η        : (x : obj C) → hom C' (fobj F x) (fobj F' x)
        η-commut : {x y : obj C} (f : hom C x y) → comp C' (η y) (farr F f)  == comp C' (farr F' f) (η x)

    open NatTrans


    

  module _ {lobj lobj' lobj'' larrow larrow' larrow''}
    {A : Category lobj larrow}
    {B : Category lobj' larrow'}
    {C : Category lobj'' larrow''} where

    Functor-∘ : Functor B C → Functor A B → Functor A C
    fobj (Functor-∘ G F) = fobj G ∘ fobj F
    farr (Functor-∘ G F) = farr G ∘ farr F
    fcomp (Functor-∘ G F) g f = ap (farr G) (fcomp F g f) ∙ fcomp G  _ _
    fid (Functor-∘ G F) x = ap (farr G) (fid F x) ∙ fid G _ 

  idF : ∀ {lobj} {larrow} (C : Category lobj larrow) → Functor C C
  fobj (idF C) = idf _
  farr (idF C) = idf _
  fcomp (idF C) f g = idp
  fid (idF C) x = idp

  module _ {lobj lobj' larrow larrow'}
    (C : Category lobj larrow)
    (D : Category lobj' larrow') where
    
    record CatEquiv : Set (lsucc (lmax (lmax lobj lobj') (lmax larrow larrow'))) where
      field
        F : Functor C D
        G : Functor D C
        F-G : Functor-∘ F G == idF D 
        G-F : Functor-∘ G F == idF C

  module _ {lobj larrow}
    (C : Category lobj larrow)
    (D : Category lobj larrow)  where

    foo3 : (C == D) ≃ CatEquiv C D
    CatEquiv.F (fst foo3 idp) = idF _
    CatEquiv.G (fst foo3 idp) = idF _
    CatEquiv.F-G (fst foo3 idp) = idp
    CatEquiv.G-F (fst foo3 idp) = idp
    is-equiv.g (snd foo3) record { F = F ; G = G ; F-G = F-G ; G-F = G-F } = {!!}
    is-equiv.f-g (snd foo3) = {!!}
    is-equiv.g-f (snd foo3) = {!!}
    is-equiv.adj (snd foo3) = {!!}

