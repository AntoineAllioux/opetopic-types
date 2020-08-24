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

  λ=↓ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : {x : A} → B x → Set k} {f g : Π A B} (h : f ∼ g)
    → {u : (x : A) →  C (f x)} {v : (x : A) →  C (g x)}
    → ((x : A) → u x == v x [ C ↓ h x ])
    → u == v [ (λ h → (x : A) → C (h x)) ↓ λ= h ]
  λ=↓ {C = C} {f = f} h {u} {v} p with λ= h | inspect λ= h
  ... | idp | ingraph q = λ= λ x → transport (λ r → u x == v x [ C  ↓ r ]) (! (app=-β h x) ∙ (ap (λ p → app= p x) q )) (p x)
{-
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

    lem : {A B C : Set} (f : A → C) (g : B → C)
      → (e : A ≃ B)
      → (h : f ∼ g ∘ (–> e)) 
      → (x : A)
      → ap f (<–-inv-l e x) ∙ (h x) == (h (<– e (–> e x))) ∙ ap g (<–-inv-r e (–> e x))
    lem {A} {B} {C} f g e h x =
      equiv-induction (λ {A} {B} e →
        (f : A → C) (g : B → C) (h : f ∼ g ∘ (–> e)) (x : A) →
          ap f (<–-inv-l e x) ∙ (h x)
          == (h (<– e (–> e x))) ∙ ap g (<–-inv-r e (–> e x))) (λ _ f g h x → ! (∙-unit-r (h x))) e f g h x

    pos-η-contr : (M : 𝕄) (i : Idx M) → is-contr (Pos M (η M i))
    pos-η-contr M i = has-level-in (η-pos M i , η-pos-elim M i _ idp)

    η-pos-map : (i : Idx M)
      → –> (pos-map f (η M i)) (η-pos M i) == η-pos N (idx-map f i) [ Pos N ↓ cns-map-η f i ]
    η-pos-map i = from-transp (Pos N) (cns-map-η f i) (contr-has-all-paths ⦃ pos-η-contr N (idx-map f i) ⦄ _ _)

 

    foo12 : {i : Idx M} (u : Pos N (cns-map f (η M i))) (v : Pos N (η N (idx-map f i)))
      → is-contr (u == v [ Pos N ↓ cns-map-η f i ])
    foo12 {i} u v = transport! is-contr (ua (to-transp-equiv (Pos N) (cns-map-η f i)))
      (=-preserves-level (pos-η-contr N (idx-map f i)))

    contr-elim : (A : Set) (B : A → Set) (A-contr : is-contr A) (d : B (contr-center A-contr)) (x : A) → B x
    contr-elim A B A-contr d x = transport B (contr-path A-contr _) d

    Pb-map' : {A : Idx M → Set} {B : Idx N → Set}
      → (g : {i : Idx M} → A i → B (idx-map f i))
      → Pb M A ⇛ Pb N B
    idx-map (Pb-map' g) (i , x) = idx-map f i , g x
    cns-map (Pb-map' {B = B} g) (c , ν) =
      let ν' p = transport B
                 (typ-map f c (<– (pos-map f c) p)
                   ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p))
                 (g (ν (<– (pos-map f _) p)))
      in cns-map f c , ν' {-
    pos-map (Pb-map' A B g) (c , _) = pos-map f c
    typ-map (Pb-map' A B g) (c , ν) p =
      let r p = typ-map f c (<– (pos-map f c) p)
                ∙ ap (Typ N (cns-map f c)) (<–-inv-r (pos-map f c) p)

          ν' : (p : Pos N (cns-map f c)) → B (Typ N (cns-map f c) p)
          ν' p = transport B (r p) (g (ν (<– (pos-map f _) p)))

          yo5 : g (ν (<– (pos-map f c) (–> (pos-map f c) p))) == g (ν p)
                  [ B ↓ (ap (idx-map f ∘ Typ M c) (<–-inv-l (pos-map f c) p)) ]
          yo5 = ↓-ap-in _ (idx-map f ∘ Typ M c)
                $ apd (g ∘ ν) (<–-inv-l (pos-map f c) p) 

          q : g (ν p)
              == transport B (r (–> (pos-map f c) p))
                             (g (ν (<– (pos-map f c) (–> (pos-map f c) p))))
              [ B ↓ typ-map f c p ]
          q = transport (λ x →
                g (ν p) == transport B x (g (ν (<– (pos-map f c) (–> (pos-map f c) p))))
                  [ B ↓ typ-map f c p ])
                        (lem _ _ (pos-map f c) (typ-map f c) p)
              $ transport (λ x → g (ν p) == x [ B ↓ typ-map f c p ])
                          (! (transp-∙ (ap (idx-map f ∘ Typ M c) (<–-inv-l (pos-map f c) p))
                                       (typ-map f c p)
                                       (g (ν (<– (pos-map f c) (–> (pos-map f c) p))))))
              $ (! $ to-transp $ yo5) ∙ᵈ transp-↓' B (typ-map f c p) _

      in pair= (typ-map f c p) q
     

            

            

            

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
