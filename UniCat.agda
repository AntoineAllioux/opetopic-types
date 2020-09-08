{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import HoTT
open import lib.NType2

module UniCat where

  -- Definition of a pre-category
  record PreCategory lobj larrow : Set (lsucc (lmax lobj larrow)) where
    infixl 40 _●_
    field
      obj       : Set lobj
      hom       : obj → obj → Set larrow
      _●_       : {x y z : obj} (g : hom y z) (f : hom x y) → hom x z
      assoc     : {x y z t : obj} (h : hom z t) (g : hom y z) (f : hom x y) → (h ● g) ● f == h ● (g ● f)
      id        : (x : obj) → hom x x
      unit-l    : {x y : obj} (f : hom x y) → (id y) ● f == f
      unit-r    : {x y : obj} (f : hom x y) → f ● (id x) == f
      homs-sets : (x y : obj) → is-set (hom x y)

  

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
    → {homs-sets : (x y : obj) → is-set (hom x y)}
    → {homs-sets₁ : (x y : obj₁) → is-set (hom₁ x y)}
    → (homs-sets= : homs-sets == homs-sets₁ [ (λ { (obj , hom) → (x y : obj) → is-set (hom x y) }) ↓ pair= obj= hom= ])
    → record { obj = obj ; hom = hom ; _●_ = comp ; id = id ; assoc = assoc ; unit-l = unit-l ; unit-r = unit-r ; homs-sets = homs-sets }
      == record { obj = obj₁ ; hom = hom₁ ; _●_ = comp₁ ; id = id₁ ; assoc = assoc₁ ; unit-l = unit-l₁ ; unit-r = unit-r₁ ; homs-sets = homs-sets₁ }
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
    → (homs-sets : (x y : obj) → is-set (hom x y))
    → (homs-sets₁ : (x y : obj₁) → is-set (hom₁ x y))
    → record { obj = obj ; hom = hom ; _●_ = comp ; id = id ; assoc = assoc ; unit-l = unit-l ; unit-r = unit-r ; homs-sets = homs-sets }
      == record { obj = obj₁ ; hom = hom₁ ; _●_ = comp₁ ; id = id₁ ; assoc = assoc₁ ; unit-l = unit-l₁ ; unit-r = unit-r₁ ; homs-sets = homs-sets₁ }
  PreCategory=' obj= hom= comp= id= assoc assoc₁ unit-l unit-l₁ unit-r unit-r₁ homs-sets homs-sets₁ =
    let assoc= = prop-has-all-paths-↓ ⦃ {!!} ⦄
        unit-r= = prop-has-all-paths-↓ ⦃ {!!} ⦄
        unit-l= = prop-has-all-paths-↓ ⦃ {!!} ⦄
        homs-sets= = prop-has-all-paths-↓ ⦃ {!!} ⦄
    in PreCategory= obj= hom= comp= id= assoc= unit-l= unit-r= homs-sets=


  module _ {lobj larrow} {P : PreCategory lobj larrow} where
  
    open PreCategory P

    -- Definition of an equivalence in a category
    record is-cat-equiv {x y : obj} (f : hom x y) : Set larrow where
      constructor mk-cat-equiv
      field
        g : hom y x
        f-g : f ● g == id y
        g-f : g ● f == id x

    is-cat-equiv= : {x y : obj} {f : hom x y}
      → {g₀ g₁ : hom y x}
      → (g₀=g₁ : g₀ == g₁)
      → {f-g₀ : f ● g₀ == id y}
      → {f-g₁ : f ● g₁ == id y}
      → (f-g₀=f-g₁ : f-g₀ == f-g₁ [ (λ g → f ● g == id y) ↓ g₀=g₁ ])
      → {g-f₀ : g₀ ● f == id x}
      → {g-f₁ : g₁ ● f == id x}
      → (g-f₀=g-f₁ : g-f₀ == g-f₁ [ (λ g → g ● f == id x) ↓ g₀=g₁ ])
      → mk-cat-equiv g₀ f-g₀ g-f₀ == mk-cat-equiv g₁ f-g₁ g-f₁
    is-cat-equiv= idp idp idp = idp

    Σ-is-cat-equiv : {x y : obj} (f : hom x y) → Σ (hom y x) (λ g → (f ● g == id y) × (g ● f == id x)) ≃ is-cat-equiv f
    Σ-is-cat-equiv f = equiv (λ { (g , f-g , g-f) → mk-cat-equiv g f-g g-f }) (λ { (mk-cat-equiv g f-g g-f) → (g , f-g , g-f) }) (λ _ → idp) λ _ → idp 
 
    _≊_ : (x y : obj) → Set larrow
    _≊_ x y = Σ (hom x y) (λ f → is-cat-equiv f)

    idi : (x : obj) → x ≊ x
    idi x = id _ , mk-cat-equiv (id _) (unit-l _) (unit-l _)

    —> : {x y : obj} (e : x ≊ y) → hom x y
    —> = fst

    <— : {x y : obj} (e : x ≊ y) → hom y x
    <— e = is-cat-equiv.g (snd e)

    <—-inv-l : {x y : obj} (e : x ≊ y)
      → (<— e) ● (—> e) == id x
    <—-inv-l e = is-cat-equiv.g-f (snd e)

    <—-inv-r : {x y : obj} (e : x ≊ y)
      → (—> e) ● (<— e) == id y
    <—-inv-r e = is-cat-equiv.f-g (snd e) 

    ≊-is-set : (x y : obj) → is-set (x ≊ y)
    ≊-is-set x y =
      let Σ-is-cat-equiv-is-set _ = Σ-level (homs-sets _ _) λ _ → Σ-level (=-preserves-level (homs-sets _ _)) λ _ → (=-preserves-level (homs-sets _ _))
      in Σ-level (homs-sets _ _) λ f → equiv-preserves-level (Σ-is-cat-equiv _) ⦃ (Σ-is-cat-equiv-is-set f) ⦄

    id-to-iso : (x y : obj) → x == y → x ≊ y
    id-to-iso x y idp = idi x

    cat-equiv-inv : {x y : obj}
      → {f : hom x y}
      → (p : is-cat-equiv f)
      → is-cat-equiv (is-cat-equiv.g p)
    is-cat-equiv.g (cat-equiv-inv {f = f} p) = f
    is-cat-equiv.f-g (cat-equiv-inv p) = is-cat-equiv.g-f p
    is-cat-equiv.g-f (cat-equiv-inv p) = is-cat-equiv.f-g p

  open PreCategory

  record Category lobj larrow : Set (lsucc (lmax lobj larrow)) where
    field
      precat    : PreCategory lobj larrow
      univalent : (x y : obj precat) → is-equiv (id-to-iso {P = precat} x y)
    open PreCategory precat public

  open Category

  module _ {l l'} (X : Category l l') where
    open Category X renaming (precat to C)

    ≊-elim : ∀ {l} {x : obj C}
      → (P : {y : obj C} → _≊_ {P = C} x y → Set l)
      → (d : P (idi x))
      → {y : obj C} (i : x ≊ y) → P i
    ≊-elim {x = x} P d {y} i =
      let u = J (λ y p → P {y} (id-to-iso x y p)) d (is-equiv.g (univalent X _ _) i)
      in transport P (is-equiv.f-g (univalent X _ _) i) u
      
    transport-iso-lem : {x y z : obj C} (f : hom C x y) (i : _≊_ {P = C} y z)
      → transport (hom C x) (is-equiv.g (univalent X y z) i) f
        == (_●_ C (fst i) f)
    transport-iso-lem {x} {y} {z} f =
      let foo = transport! (λ p → transport (hom C x) p f == fst (idi y) ● f) (is-equiv.g-f (univalent X y y) idp) (! (unit-l C f))
      in ≊-elim (λ {z} i → transport (hom C x) (is-equiv.g (univalent X y z) i) f == _●_ C (fst i) f) foo


  module _ {lobj lobj' larrow larrow'} (Cat : Category lobj larrow) (Cat' : Category lobj' larrow') where

    open Category Cat renaming (precat to C)
    open Category Cat' renaming (precat to C')   

    record Functor : Set (lsucc (lmax (lmax lobj lobj') (lmax larrow larrow'))) where
      field
        fobj  : obj C → obj C'
        farr  : {x y : obj C} → hom C x y → hom C' (fobj x) (fobj y)
        fcomp : {x y z : obj C} (f : hom C x y) (g : hom C y z) → farr (_●_ C g f) == _●_ C' (farr g) (farr f) 
        fid   : (x : obj C) → farr (id C x) == id C' (fobj x)

    open Functor public

    record NatTrans (F F' : Functor) : Set (lsucc (lmax (lmax lobj lobj') (lmax larrow larrow'))) where
      field
        η        : (x : obj C) → hom C' (fobj F x) (fobj F' x)
        η-commut : {x y : obj C} (f : hom C x y) → _●_ C' (η y) (farr F f)  == _●_ C' (farr F' f) (η x)

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

