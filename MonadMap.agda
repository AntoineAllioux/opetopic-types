{-# OPTIONS --without-K --rewriting --allow-unsolved-meta --allow-incomplete-matches
 #-}

open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import HoTT
open import Utils

module MonadMap where

  module _ {i j} {A : Set i} {B : A → Set j} where

    data Graph (f : ∀ x → B x) (x : A) (y : B x) : Set j where
      ingraph : f x == y → Graph f x y

    inspect : (f : ∀ x → B x) (x : A) → Graph f x (f x)
    inspect _ _ = ingraph idp
{-
  λ=↓ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : {x : A} → B x → Set k} {f g : Π A B} (h : f ∼ g)
    → {u : (x : A) →  C (f x)} {v : (x : A) →  C (g x)}
    → ((x : A) → u x == v x [ C ↓ h x ])
    → u == v [ (λ h → (x : A) → C (h x)) ↓ λ= h ]
  λ=↓ {C = C} {f = f} h {u} {v} p with λ= h | inspect λ= h
  ... | idp | ingraph q = λ= λ x → transport (λ r → u x == v x [ C  ↓ r ]) (! (app=-β h x) ∙ (ap (λ p → app= p x) q )) (p x)
-}
  λ=↓ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : {x : A} → B x → Set k} {f g : Π A B} (h : f == g)
    → {u : (x : A) →  C (f x)} {v : (x : A) →  C (g x)}
    → ((x : A) → u x == v x [ C ↓ app= h x ])
    → u == v [ (λ h → (x : A) → C (h x)) ↓ h ]
  λ=↓ {C = C} {f = f} idp {u} {v} = λ=
{-
  λ=↓' : ∀ {i j k} {A : Set i} {B : A → Set j} {C : {x : A} → B x → Set k} {x y : A} (h : x == y)
    → {u : Π (B x) C } {v : Π (B y) C}
    → ((x : A) → u x == v x [ C x ↓ h ])
    → u == v [ (λ x → (y : B x) → C y) ↓ h ]
  λ=↓' idp = λ= 

  λ=↓' : ∀ {i j k} {A : Set i} {B : A → Set j} {C : {x : A} → B x → Set k} {f g : Π A B} (h : f ∼ g)
    → {u : (x : A) →  C (f x)} {v : (x : A) →  C (g x)}
    → ((x : A) → u x == v x [ C ↓ h x ])
    → u == v [ (λ x → (y : B x) → C (h x)) ↓ λ= h ]
  λ=↓' = ?
-}

  _⇒_ : {A : Set} (B C : A → Set) → Set
  _⇒_ {A} B C = (x : A) → B x → C x

  transp!-∙ : ∀ {i j} {A : Type i} {B : A → Type j} {x y z : A}
    (p : x == y) (q : z == y) (b : B x)
    → transport B (p ∙ ! q) b == transport! B q (transport B p b)
  transp!-∙ idp idp b = idp

  C-transp : {A : Set} {B : A → Set} (C : {x : A} → B x → Set)
    → {x y : A} (p : x == y)
    → {u : B x} {v : B y}
    → (q : u == v [ B ↓ p ])
    → C u == C v
  C-transp C idp q = ap C q

  C-transp' : {A : Set} {B : A → Set} (C : {x : A} → B x → Set)
    → {x y : A} (p : x == y)
    → (u : B y)
    → C (transport B (! p) u) == C u
  C-transp' {B = B} C p u = C-transp C p (transp-↓ B p u)

  C-transp'' : {A : Set} {B : A → Set} (C : {x : A} → B x → Set)
    → {x y : A} (p : x == y)
    → (u : B x)
    → C (transport B p u) == C u
  C-transp'' {B = B} C idp u = idp -- C-transp C p (transp-↓ B p u) 

  coe-coe! : {A B : Set} (p : A == B) (x : B) → coe (! p) x == coe! p x
  coe-coe! idp x = idp

  transp-transp! : {A : Set} {B : A → Set} {x y : A}
    → (p : x == y) (u : B y) → transport B (! p) u == transport! B p u
  transp-transp! idp u = idp

  transport-elim : {A : Set} {B : A → Set} (C : {x : A} → B x → Set)
    → {x y : A} (p : x == y) (u : B x)
    → C (transport B p u) → C u
  transport-elim C idp u x = {!!}

  transp-pos-invar : (M : 𝕄) {i j : Idx M} (c : Cns M i)
    → (p : i == j) 
    → Pos M (transport (Cns M) p c) == Pos M c 
  transp-pos-invar M c idp = idp
{-
  transp-↓' : ∀ {i j} {A : Type i} (P : A → Type j) {a₁ a₂ : A}
    → (p : a₁ == a₂) (y : P a₁) → y == transport P p y  [ P ↓ p ]
  transp-↓' _ idp _ = idp
-}
  record Map (M N : 𝕄) : Set where
    field
      idx-map : Idx M → Idx N
      cns-map : {i : Idx M} → Cns M i → Cns N (idx-map i)
      pos-map : {i : Idx M} (c : Cns M i)
        → Pos M c ≃ Pos N (cns-map c)
      typ-map : {i : Idx M} (c : Cns M i) (p : Pos M c)
        → idx-map (Typ M c p) == Typ N (cns-map c) (–> (pos-map c) p)

    δ-map : {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos N (cns-map c))
      → Cns N (Typ N (cns-map c) p)
    δ-map c δ p =
      transport (Cns N)
                (typ-map _ (<– (pos-map c) p)
                 ∙ ap (Typ N (cns-map c)) (<–-inv-r (pos-map c) p))
                (cns-map (δ (<– (pos-map _) p)))

    δ-map-pos : {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M c) (q : Pos M (δ p))
      → Pos N (transport (Cns N)
                         (typ-map c (<– (pos-map c) (–> (pos-map c) p))
                          ∙ ap (Typ N (cns-map c)) (<–-inv-r (pos-map c) (–> (pos-map c) p)))
                         (cns-map (δ (<– (pos-map c) (–> (pos-map c) p))))) 
    δ-map-pos c δ p q =
      coe (! (transp-pos-invar N (cns-map (δ (<– (pos-map c) (–> (pos-map c) p)))) _))
          (–> (pos-map (δ (<– (pos-map c) (–> (pos-map c) p))))
              (transport (Pos M ∘ δ) (! (<–-inv-l (pos-map c) p)) q)) 
    
    field
      cns-map-η : (i : Idx M) → cns-map (η M i) == η N (idx-map i)
      cns-map-μ : {i : Idx M} (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → cns-map (μ M c δ)
          == μ N (cns-map c) (δ-map c δ)
      μ-pos-map : {i : Idx M} (c : Cns M i) (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos M c) (q : Pos M (δ p))
        → –> (pos-map (μ M c δ)) (μ-pos M c δ p q)
            == μ-pos N (cns-map c) (δ-map c δ)
                       (–> (pos-map c) p)
                       (δ-map-pos c δ p q)
            [ Pos N ↓ cns-map-μ c δ ]
    {-  μ-pos-fst-map : {i : Idx M} (c : Cns M i) (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos M (μ M c δ))
        → –> (pos-map c) (μ-pos-fst M c δ p) == μ-pos-fst N (cns-map c) (δ-map c δ) (transport (Pos N) (cns-map-μ c δ) (–> (pos-map (μ M c δ)) p))
      μ-pos-snd-map : {i : Idx M} (c : Cns M i) (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos M (μ M c δ))
        → –> (pos-map (δ (μ-pos-fst M c δ p))) (μ-pos-snd M c δ p)
          == μ-pos-snd N (cns-map c) (δ-map c δ) (transport (Pos N) (cns-map-μ c δ) (–> (pos-map (μ M c δ)) p)) [ Pos N ↓ {!!} ] -}

  module _ (M N : 𝕄) (f : Map M N) where

    open Map f

    μ-pos-fst-map : {i : Idx M} (c : Cns M i) (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos M (μ M c δ))
        → –> (pos-map c) (μ-pos-fst M c δ p)
          == μ-pos-fst N (cns-map c)
                         (δ-map c δ)
                         (transport (Pos N) (cns-map-μ c δ) (–> (pos-map (μ M c δ)) p))
    μ-pos-fst-map c δ p =
      let foo : –> (pos-map (μ M c δ)) p -- (μ-pos M c δ p q)
                == μ-pos N (cns-map c) (δ-map c δ) (–> (pos-map c) (μ-pos-fst M c δ p)) {!!} [ Pos N ↓ cns-map-μ c δ ]
          foo = μ-pos-map c δ (μ-pos-fst M c δ p) (μ-pos-snd M c δ p)

          foo2 : {!!} == –> (pos-map c) (μ-pos-fst M c δ p) [ {!!} ↓ {!!} ]
          foo2 = ap↓ (λ { (c , δ , p) → μ-pos-fst N c δ p}) (pair= (cns-map-μ c δ) (↓-Σ-in {!!} {!!}))

          bar : –> (pos-map c) (μ-pos-fst M c δ p)
                == μ-pos-fst N (cns-map c) (δ-map c δ) (transport (Pos N) (cns-map-μ c δ) (–> (pos-map (μ M c δ)) p))
          bar = {!!}
      in {!!}
    

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
  open _⇛_ public

  

  module _ {M N : 𝕄} (f : M ⇛ N) where

    pos-η-contr : (M : 𝕄) (i : Idx M) → is-contr (Pos M (η M i))
    pos-η-contr M i = has-level-in (η-pos M i , η-pos-elim M i _ idp)

    η-pos-map : (i : Idx M)
      → –> (pos-map f (η M i)) (η-pos M i) == η-pos N (idx-map f i) [ Pos N ↓ cns-map-η f i ]
    η-pos-map i = from-transp (Pos N) (cns-map-η f i) (contr-has-all-paths ⦃ pos-η-contr N (idx-map f i) ⦄ _ _)

  module _ {M N : 𝕄}
           (f : M ⇛ N) where

    

    foo16 : {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M c) (q : Pos M (δ p))
      → Pos N
      (transport (Cns N)
       (typ-map f c (<– (pos-map f c) (–> (pos-map f c) p)) ∙
        ap (Typ N (cns-map f c))
        (<–-inv-r (pos-map f c) (–> (pos-map f c) p)))
       (cns-map f (δ (<– (pos-map f c) (–> (pos-map f c) p)))))
    foo16 c δ p q =
      let foo17 = –> (pos-map f (δ p)) q
      
          foo18 : idx-map f (Typ M c (<– (pos-map f c) (–> (pos-map f c) p)))
                  == Typ N (cns-map f c) (–> (pos-map f c) p)
          foo18 = typ-map f c (<– (pos-map f c) (–> (pos-map f c) p))
                  ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) (–> (pos-map f c) p))

          foo19 : Pos N (cns-map f (δ (<– (pos-map f c) (–> (pos-map f c) p))))
          foo19 = –> (pos-map f (δ _)) (transport (Pos M ∘ δ) (! (<–-inv-l (pos-map f c) p)) q)
      in coe (! (transp-pos-invar N (cns-map f (δ _)) foo18)) foo19

    foo14 : {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M c) (q : Pos M (δ p))
      → –> (pos-map f (μ M c δ)) (μ-pos M c δ p q) ==
          μ-pos N (cns-map f c)
                  (λ p → transport (Cns N) (typ-map f _ (<– (pos-map f c) p) ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p)) (cns-map f (δ (<– (pos-map f _) p))))
                  (–> (pos-map f c) p)
                  {!–> (pos-map f (δ p)) ?!} [ Pos N ↓ cns-map-μ f c δ ]
    foo14 = {!!}


  foo15 : {M : 𝕄} (i : Idx M) (c : Cns M i) (δ : (p : Pos M c) → Cns M (Typ M c p))
    → (Σ (Pos M c) λ p → Pos M (δ p)) ≃ Pos M (μ M c δ) 
  foo15 {M} i c δ = equiv (uncurry (μ-pos M c δ))
                          (λ p → μ-pos-fst M c δ p , μ-pos-snd M c δ p)
                          (λ p → idp)
                          λ p → idp

  foo2 : {A : Set} {B : A → Set}
    → {C : A → Set} {D : (x : A) (y : B x) (z : C x) → Set}
    → {x x₁ : A} {y : B x} {y₁ : B x₁}
    → (p : (x , y) == (x₁ , y₁))
    → (u : Σ (C x) (D x y))
    → transport C (fst= p) (fst u) == fst (transport (λ { (x , y) → Σ (C x) (D x y) }) p u)
  foo2 {C = C} {D} {x} {x₁} {y} {y₁} p u =
    to-transp $ ↓-ap-in _ fst $ ap↓ fst $ transp-↓' (λ { (x , y) → Σ (C x) (D x y) }) p u  

  foo3 : {A : Set} {B : A → Set}
    → {C : A → Set} {D : (x : A) (y : B x) (z : C x) → Set}
    → {x x₁ : A} {y : B x} {y₁ : B x₁}
    → (p : x == x₁) (q : y == y₁ [ B ↓ p ])
    → (u : C x) (v : D x y u)
    → transport C p u == fst (transport (λ { (x , y) → Σ (C x) (D x y) }) (pair= p q) (u , v))
  foo3 {C = C} {D} {x} {x₁} {y} {y₁} idp idp u v = idp

  foo4 : {A B : Set}
    → {C : B → Set}
    → (f : A → B)
    → (g : Π B C)
    → {x x₁ : A} {y : B} {y₁ : B}
    → (p : x == x₁)
    → ap (λ x → f x , g (f x)) p == pair= (ap f p) (apd g (ap f p))
  foo4 f g idp = idp
 
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

 
{-
    foo12 : {i : Idx M} (u : Pos N (cns-map f (η M i))) (v : Pos N (η N (idx-map f i)))
      → is-contr (u == v [ Pos N ↓ cns-map-η f i ])
    foo12 {i} u v = transport! is-contr (ua (to-transp-equiv (Pos N) (cns-map-η f i)))
      (=-preserves-level (pos-η-contr N (idx-map f i)))
-}
    contr-elim : (A : Set) (B : A → Set) (A-contr : is-contr A) (d : B (contr-center A-contr)) (x : A) → B x
    contr-elim A B A-contr d x = transport B (contr-path A-contr _) d

    htpy-naturality : {A B : Set}
      → {f g : A → B}
      → (H : f ∼ g)
      → {x y : A} (p : x == y)
      → ap f p ∙ H y == H x ∙ ap g p
    htpy-naturality H {x} idp = ! (∙-unit-r (H x))

    Π-pth : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
      → {x y : A}
      → (f : Π (B x) (C x))
      → (p : x == y)
      → transport (λ x → Π (B x) (C x)) p f
        == λ x → transport (uncurry C) (pair= p (transp-↓ B p x)) (f (transport B (! p) x))
    Π-pth f idp = ↓-Π-in  {!!}

    η-pos-is-contr : {M : 𝕄} (i : Idx M) → is-contr (Pos M (η M i))
    η-pos-is-contr {M} i = has-level-in (η-pos M i , η-pos-elim M i (λ p → η-pos M i == p) idp)

    contr-has-all-paths-↓ : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} {p : x == y} {u : B x} {v : B y}
      {{_ : is-contr (B y)}} → u == v [ B ↓ p ]
    contr-has-all-paths-↓ {p = idp} = contr-has-all-paths _ _

    Pb-map' : {A : Idx M → Set} {B : Idx N → Set}
      → (g : {i : Idx M} → A i → B (idx-map f i))
      → Pb M A ⇛ Pb N B
    idx-map (Pb-map' g) (i , x) = idx-map f i , g x
    cns-map (Pb-map' {B = B} g) (c , ν) =
      let ν' p = transport B
                 (typ-map f c (<– (pos-map f c) p)
                   ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p))
                 (g (ν (<– (pos-map f _) p)))

          foo : (p : Pos N (cns-map f c)) → {!!} -- ν' p == g (ν ?)
          foo = {!!}
      in cns-map f c , ν' 
    pos-map (Pb-map' g) (c , _) = pos-map f c
    typ-map (Pb-map' {A = A} {B} g) (c , ν) p =
      let p' = <– (pos-map f c) (–> (pos-map f c) p)

          pth q = ap (λ p → idx-map f (Typ M c p)) (! (<–-inv-l (pos-map f c) p))
            ∙ typ-map f c p'
            ∙ q

          pth₂ = typ-map f c p'
            ∙ ap (Typ N (cns-map f c))
                 (<–-inv-r (pos-map f c) (–> (pos-map f c) p))

          htpy-nat-lem : {A B : Set}
            → {f g : A → B}
            → (H : f ∼ g)
            → {x y : A} (p : x == y)
            → ap f (! p) ∙ H x ∙ ap g p == H y
          htpy-nat-lem H = λ { idp → ∙-unit-r _ }
          
          pth₃ =
            pth (ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) (–> (pos-map f c) p)))
              =⟨ ap pth (ap (ap (Typ N (cns-map f c))) (! (<–-inv-adj (pos-map f c) p)))  ⟩
            pth (ap (Typ N (cns-map f c)) (ap (–> (pos-map f c)) (<–-inv-l (pos-map f c) p)))
              =⟨ ap pth (∘-ap (Typ N (cns-map f c)) (–> (pos-map f c)) (<–-inv-l (pos-map f c) p)) ⟩
            pth (ap (λ p → Typ N (cns-map f c) (–> (pos-map f c) p)) (<–-inv-l (pos-map f c) p))
              =⟨ htpy-nat-lem (typ-map f c) (<–-inv-l (pos-map f c) p) ⟩
            typ-map f c p =∎

          P q = g (ν p) == transport B pth₂ (g (ν p')) [ B ↓ q ]

          goal-aux : P (pth (ap (Typ N (cns-map f c))
                                (<–-inv-r (pos-map f c) (–> (pos-map f c) p)))) 
          goal-aux = ↓-ap-in B _ (apd (g ∘ ν) (! (<–-inv-l (pos-map f c) p)))
                     ∙ᵈ transp-↓' B pth₂ (g (ν p'))

          goal : P (typ-map f c p)
          goal = transport P pth₃ goal-aux
          
      in pair= (typ-map f c p) goal
    cns-map-η (Pb-map' {A = A} {B} g) (i , x) =
      let foo = {!!}

          P c = {!!} 

          goal : P (cns-map-η f i)
          goal = {!!}

          pth : (p : Pos N (cns-map f (η M i)))
            → idx-map f i == Typ N (cns-map f (η M i)) p
          pth p = (typ-map f (η M i))
                   (<– (pos-map f (η M i)) p)
                    ∙
                     ap (Typ N (cns-map f (η M i)))
                      (<–-inv-r (pos-map f (η M i)) p)

          pth2 : idx-map f i == Typ N (cns-map f (η M i)) (–> (pos-map f (η M i)) (η-pos M i))
          pth2 = typ-map f (η M i)
                   (<– (pos-map f (η M i)) (–> (pos-map f (η M i)) (η-pos M i)))
                    ∙
                     ap (Typ N (cns-map f (η M i)))
                      (<–-inv-r (pos-map f (η M i)) (–> (pos-map f (η M i)) (η-pos M i)))

          pth3 : idx-map f i == Typ N (cns-map f (η M i)) (–> (pos-map f (η M i)) (η-pos M i))
          pth3 = ap (idx-map f ∘ (Typ M (η M i))) (<–-inv-l (pos-map f (η M i)) (η-pos M i)) ∙
                 typ-map f (η M i) (η-pos M i)

          foo : {p : Pos N (cns-map f (η M i))}
            → {p' : Pos N (η N (idx-map f i))}
            → (q : p == p' [ (Pos N) ↓ (cns-map-η f i) ])
            → ap (uncurry (Typ N)) (pair= (cns-map-η f i) q) == ! (pth p)
          foo = {!!}

          foo2 : {p : Pos N (cns-map f (η M i))}
            → (q : p == η-pos N (idx-map f i) [ (Pos N) ↓ (cns-map-η f i) ])
            → ap (uncurry (Typ N)) (pair= (cns-map-η f i) q) == ! (pth p)
          foo2 = {!!}

          foo4 : –> (pos-map f (η M i)) (η-pos M i) == η-pos N (idx-map f i) [ (Pos N) ↓ (cns-map-η f i) ]
          foo4 = {!!}

          foo3 : (q : –> (pos-map f (η M i)) (η-pos M i) == η-pos N (idx-map f i) [ (Pos N) ↓ (cns-map-η f i) ])
            → ap (uncurry (Typ N)) (pair= (cns-map-η f i) q) == ! pth2
          foo3 = {!!} 


          

          goal4 : {t : Pos N (cns-map f (η M i))}
            → (q : t == η-pos N (idx-map f i) [ (Pos N) ↓ (cns-map-η f i) ])
            → (transport B
                (pth t)
                (g x)) ==
                (g x) [ uncurry (λ a z → B (Typ N a z)) ↓ pair= (cns-map-η f i) q ]
          goal4 q = {!!}


          goal3 : {t : Pos N (cns-map f (η M i))}
            → {t' : Pos N (η N (idx-map f i))}
            → (q : t == t' [ (Pos N) ↓ (cns-map-η f i) ])
            → (transport B (pth t) (g x))
               == (g x) [ (uncurry (λ a z → B (Typ N a z))) ↓ pair= (cns-map-η f i) q ]
          goal3 q = {!!} -- ↓-ap-out B (uncurry (Typ N)) (pair= (cns-map-η f i) q) (contr-has-all-paths-↓ ⦃ {!η-pos-is-contr!} ⦄)


          goal2 : (λ p → transport B (pth p) (g x))
                  == cst (g x)
                  [ (λ c → (p : Pos N c) → B (Typ N c p)) ↓ cns-map-η f i ]
          goal2 = ↓-Π-in goal3 
      in pair= (cns-map-η f i) goal2
  {-
    cns-map-η (Pb-map' A B g) (i , x) =
      let {- foo9 : (u : Pos N (cns-map f (η M i))) (v : Pos N (η N (idx-map f i)))
            → u == v [ Pos N ↓ cns-map-η f i ]
          foo9 u v = from-transp (Pos N) (cns-map-η f i) (contr-has-all-paths ⦃ pos-η-contr N (idx-map f i) ⦄ _ _)
{-
          foo13 : (i : Idx M) (c : Cns M i) (p : Pos M c)
            → idx-map f (Typ M c p) == Typ N (cns-map f c) (–> (pos-map f c) p)
          foo13 = {!idx-map !}

          foo12 : Typ N (cns-map f (η M i)) (–> (pos-map f _) (η-pos M i))
                  == idx-map f i -- Typ N (η N (idx-map f i)) (η-pos N (idx-map f i))
          foo12 = ap (uncurry (Typ N)) (pair= (cns-map-η f i) (η-pos-map i))
-}
          foo11 : _==_ {A = idx-map f i == Typ N (cns-map f (η M i)) (–> (pos-map f _) (η-pos M i))}
              (typ-map f (η M i) (η-pos M i))
              (! (ap (uncurry (Typ N)) (pair= (cns-map-η f i) (η-pos-map i))))
          foo11 = {!!}

          foo10 : _==_ {A = idx-map f i == Typ N (cns-map f (η M i)) (–> (pos-map f _) (η-pos M i))}
                (typ-map f (η M i) (<– (pos-map f (η M i)) (–> (pos-map f _) (η-pos M i))) ∙ ap (Typ N (cns-map f (η M i))) (<–-inv-r (pos-map f (η M i)) (–> (pos-map f _) (η-pos M i))))
              (! (ap (uncurry (Typ N)) (pair= (cns-map-η f i) (η-pos-map i))))
          foo10 = {!!}

          foo6 : {u : Pos N (cns-map f (η M i))} {v : Pos N (η N (idx-map f i))}
            → (q : u == v [ Pos N ↓ cns-map-η f i ])
            → _==_ {A = idx-map f i == Typ N (cns-map f (η M i)) u}
              (typ-map f (η M i) (<– (pos-map f (η M i)) u) ∙ ap (Typ N (cns-map f (η M i))) (<–-inv-r (pos-map f (η M i)) u))
              (! (ap (uncurry (Typ N)) (pair= (cns-map-η f i) q)))
          foo6 q = {!transport  !}

          foo5 : {u : Pos N (cns-map f (η M i))} {v : Pos N (η N (idx-map f i))}
            → (q : u == v [ Pos N ↓ cns-map-η f i ])
            → transport B (typ-map f (η M i) (<– (pos-map f (η M i)) u)
                ∙ ap (Typ N (cns-map f (η M i))) (<–-inv-r (pos-map f (η M i)) u)) (g x)
              == g x [ B ↓ ap (uncurry (Typ N)) (pair= (cns-map-η f i) q) ]
          foo5 {u} {v} q = transport! (λ p → transport B p (g x) == g x [ B ↓ ap (uncurry (Typ N)) (pair= (cns-map-η f i) q) ])  (foo6 q) (transp-↓ B (ap (uncurry (Typ N)) (pair= (cns-map-η f i) q)) (g x))

          foo4 : {u : Pos N (cns-map f (η M i))} {v : Pos N (η N (idx-map f i))}
            → (q : u == v [ Pos N ↓ cns-map-η f i ])
            → transport B (typ-map f (η M i) (<– (pos-map f (η M i)) u) ∙ ap (Typ N (cns-map f (η M i))) (<–-inv-r (pos-map f (η M i)) u)) (g x)
              == g x [ (λ { (x , u) → B (Typ N x u) }) ↓ pair= (cns-map-η f i) q ]
          foo4 q = ↓-ap-out B (uncurry (Typ N)) (pair= (cns-map-η f i) q) (foo5 q)
-}
          foo : (λ p → transport B (typ-map f (η M i) (<– (pos-map f (η M i)) p) ∙ ap (Typ N (cns-map f (η M i))) (<–-inv-r (pos-map f (η M i)) p)) (g x))
                == (λ _ → g x) [ (λ c → (p : Pos N c) → B (Typ N c p)) ↓ cns-map-η f i ]
          foo = ↓-Π-in {!!} -- foo4
          
           
      in pair= (cns-map-η f i) foo
    cns-map-μ (Pb-map' A B g) {i} (c , c₁) δ =
      let 
{-
          bar3 : (p : Pos N (cns-map f c)) → transport (Cns N)
            (typ-map f c (is-equiv.g (snd (pos-map f c)) p) ∙ ap (Typ N (cns-map f c)) (is-equiv.f-g (snd (pos-map f c)) p))
            (cns-map f (fst (δ (is-equiv.g (snd (pos-map f c)) p))))
            == transport (Cns N)
            (typ-map f c (is-equiv.g (snd (pos-map f c)) p))
            (cns-map f (fst (δ (is-equiv.g (snd (pos-map f c)) p))))
          bar3 p = ?
  -}      

          foo : (p : Pos N (cns-map f c))
              → transport (Cns N) (typ-map f c (<– (pos-map f c) p) ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p)) (cns-map f (fst (δ (<– (pos-map f c) p))))
                == fst (transport (Cns (Pb N B))
                                  (typ-map (Pb-map' A B g) {i} (c , c₁) (<– (pos-map (Pb-map' A B g) {i} (c , c₁)) p) ∙ ap (Typ (Pb N B) {idx-map (Pb-map' A B g) i} (cns-map (Pb-map' A B g) {i} (c , c₁))) (<–-inv-r (pos-map (Pb-map' A B g) {i} (c , c₁)) p))
                                  (cns-map (Pb-map' A B g) {Typ M c (<– (pos-map f c) p) , c₁ _} (δ (<– (pos-map (Pb-map' A B g) {i} (c , c₁)) p))))
                                  
          foo p = {!!} {-
            let bar1 = typ-map f c (is-equiv.g (snd (pos-map f c)) p)
                       ∙ ap (Typ N (cns-map f c)) (is-equiv.f-g (snd (pos-map f c)) p)
                bar2 = 
               {- bar2 = _ ∙ ap (λ p₁ → transport B
                  (typ-map f c (is-equiv.g (snd (pos-map f c)) p₁) ∙
                  ap (Typ N (cns-map f c)) (is-equiv.f-g (snd (pos-map f c)) p₁))
                  (g (c₁ (is-equiv.g (snd (pos-map f c)) p₁)))) (<–-inv-r (pos-map f c) p) -}
                u = cns-map f (fst (δ (<– (pos-map f c) p))) 
            in transport (Cns N)
                 bar1
                 u
                 =⟨ foo3 _ _ _ _ ⟩
               fst (transport (Cnsₚ N B) (pair= bar1 {!!}) (u , _))
               =⟨ ap (λ x → fst (transport (Cnsₚ N B) {!!} {!!})) (! (Σ-∙ {!!} {!!})) ⟩
               fst (transport (Cnsₚ N B) (pair= {!!} {!!} ∙ pair= {!!} {!!}) (u , _))
               =⟨ {!!} ⟩
               fst (transport (Cnsₚ N B) (pair= {!!} {!!} ∙ pair= {!!} {!!}) (u , _)) =∎ -}
      in {!!} -- pair= (cns-map-μ f c (fst ∘ δ) ∙  ap (μ N (cns-map f c)) (λ= foo)) {!!}
-}
    cns-mapₛ : {i : Idxₛ M} → Cnsₛ M i → Cnsₛ N (idx-map f (fst i) , cns-map f (snd i))
    cns-mapₛ (lf i) = transport (λ x → Cnsₛ N (idx-map f i , x)) (! (cns-map-η f i)) (lf (idx-map f i))
    cns-mapₛ {.(_ , μ M c δ)} (nd c δ ε) =
      let hyp p = cns-mapₛ (ε p)
            
          δ₁ p = cns-map f (δ (<– (pos-map f c) p ))
                 |> transport (Cns N)
                              ((typ-map f c (<– (pos-map f _) p)
                                ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p)))

          ε₁ p = cns-mapₛ (ε (<– (pos-map f c) p))
                 |> transport (Pd N)
                              (pair= (typ-map f c _
                                     ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p))
                                     (transp-↓' _ _ _))
      in nd (cns-map f c) δ₁ ε₁
         |> transport (λ x → Cnsₛ N (idx-map f _ , x))
                      (! (cns-map-μ f c δ))
                          

    pos-mapₛ : {i : Idxₛ M} (c : Cnsₛ M i) → Posₛ M c ≃ Posₛ N (cns-mapₛ c)
    pos-mapₛ {i} c = g c , is-eq (g c) (h c) (g-h c) (h-g c)
      where g : {i : Idxₛ M} (c : Cnsₛ M i) → Posₛ M c → Posₛ N (cns-mapₛ c)
            g (lf i) ()
            g {i , _} (nd c δ ε) (inl x) = coe (! (C-transp' {B = (λ x₁ → Cnsₛ N (idx-map f i , x₁))} (Posₛ N) (cns-map-μ f c δ) _)) (inl x)
            g {i , _} (nd c δ ε) (inr (p , q)) =
              let q' = coe! (C-transp'' {B = Cnsₛ N} (Posₛ N) _ (cns-mapₛ (ε (<– (pos-map f c) (–> (pos-map f c) p)))))
                            (transport! (Posₛ N ∘ cns-mapₛ ∘ ε) (<–-inv-l (pos-map f c) p) (g _ q))
              in coe! (C-transp' {B = (λ x₁ → Cnsₛ N (idx-map f i , x₁))} (Posₛ N) (cns-map-μ f c δ) _)
                      (inr (–> (pos-map f c) p , q'))

            h : {i : Idxₛ M} (c : Cnsₛ M i) → Posₛ N (cns-mapₛ c) → Posₛ M c
            h (lf i) p = coe (C-transp'' (Posₛ N) (! (cns-map-η f i)) (lf (idx-map f i))) p
            h (nd c δ ε) p with coe (C-transp'' (Posₛ N) (! (cns-map-μ f c δ)) _) p
            ... | inl x = inl x
            ... | inr (p' , q) =
              let q' = h (ε (<– (pos-map f c) p')) (coe (C-transp'' (Posₛ N) _ (cns-mapₛ (ε (<– (pos-map f c) p')))) q)
              in inr (<– (pos-map f c) p' , q')

            g-h : {i : Idxₛ M} (c : Cnsₛ M i) → (g c) ∘ (h c) ∼ idf _
            g-h (lf i) p = ⊥-elim {P = λ _ → g (lf i) (h (lf i) p) == p} (coe (C-transp'' (Posₛ N) (! (cns-map-η f i)) (lf (idx-map f i))) p)
            g-h (nd c δ ε) p with coe (C-transp'' (Posₛ N) (! (cns-map-μ f c δ)) _) p
            ... | inl x = {!C-transp'' ? ? ?!}
            ... | inr (p' , q) = {!!}

            h-g : {i : Idxₛ M} (c : Cnsₛ M i) → (h c) ∘ (g c) ∼ idf _
            h-g (nd c δ ε) (inl x) = {!!}
            h-g (nd c δ ε) (inr (p , q)) = {!!}
              
    Slice-map : Slice M ⇛ Slice N 
    idx-map Slice-map (i , c) = idx-map f i , cns-map f c
    cns-map Slice-map = cns-mapₛ
{-  pos-map Slice-map = pos-mapₛ
    typ-map Slice-map c p =
      let foo : idx-map f (fst (Typₛ M c p)) == fst (Typₛ N (cns-mapₛ c) (–> (pos-mapₛ c) p))
          foo = foo11 _ _ _
      in pair= foo {!!}
      where foo11 : (i : Idxₛ M) (c : Pd M i) (p : Posₛ M c) → idx-map f (fst (Typₛ M c p)) == fst (Typₛ N (cns-mapₛ c) (–> (pos-mapₛ c) p))
            foo11 .(_ , μ M c δ) (nd c δ ε) (inl x) = {!!}
            foo11 .(_ , μ M c δ) (nd c δ ε) (inr (p , q)) =
              let hyp = foo11 _ (ε p) q
              in {!!}
    cns-map-η Slice-map = {!!}
    cns-map-μ Slice-map = {!!}
  -}


  -- OpetopicType is contrafunctorial
  {-# TERMINATING #-}
  OpType-map : {M N : 𝕄}
    → (f : M ⇛ N)
    → OpetopicType N
    → OpetopicType M
  Ob (OpType-map f X) x = Ob X (idx-map f x)
  Hom (OpType-map f X) = OpType-map (Slice-map (Pb-map' f (idf _))) (Hom X)


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

