{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import MiniUniverse
open import AbsoluteOpetopicTypes
open import DependentOpetopicType

module Map where

  -- Utils
  
  contr-has-all-paths-↓ : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} {p : x == y} {u : B x} {v : B y}
      {{_ : is-contr (B y)}} → u == v [ B ↓ p ]
  contr-has-all-paths-↓ {p = idp} = contr-has-all-paths _ _

  Lift-preserves-level : ∀ {i j} {n} {A : Set i} → has-level n A → has-level n (Lift {j = j} A)
  Lift-preserves-level p = {!!}

  -- Some lemmas about the eliminators
  
  ⊔ₚ-Frm-rec-lem : ∀ {ℓ} {n : ℕ} {X Y : 𝕆 ℓ n}
      → {U V : ℙ}
      → (inlₚ* : El U → Frm X)
      → (inrₚ* : El V → Frm X)
      → (g : Frm X → Frm Y)
      → g ∘ (⊔ₚ-Frm-rec inlₚ* inrₚ*) == ⊔ₚ-Frm-rec (g ∘ inlₚ*) (g ∘ inrₚ*)
  ⊔ₚ-Frm-rec-lem {U = U} {V} inlₚ* inrₚ* g =
    let P p = g (⊔ₚ-Frm-rec inlₚ* inrₚ* p) == ⊔ₚ-Frm-rec (g ∘ inlₚ*) (g ∘ inrₚ*) p
    in λ= (⊔ₚ-elim {U = U} {V} P (λ _ → idp) (λ _ → idp))

  Σₚ-Frm-rec-lem : ∀ {ℓ} {n : ℕ} {X Y : 𝕆 ℓ n}
      → {U : ℙ} {V : El U → ℙ}
      → (ρ : (u : El U) → El (V u) → Frm X)
      → (g : Frm X → Frm Y)
      → g ∘ (Σₚ-Frm-rec ρ) == Σₚ-Frm-rec λ p q → g (ρ p q)
  Σₚ-Frm-rec-lem {U = U} {V} ρ g =
    let P p = g (Σₚ-Frm-rec ρ p) == Σₚ-Frm-rec (λ p q → g (ρ p q)) p
    in λ= (Σₚ-elim U V P λ _ _ → idp)

  ⊤ₚ-Frm-rec-lem : ∀ {ℓ} {n : ℕ} {X Y : 𝕆 ℓ n}
      → (f : Frm X)
      → (g : Frm X → Frm Y)
      → g ∘ (⊤ₚ-Frm-rec f) == ⊤ₚ-Frm-rec (g f)
  ⊤ₚ-Frm-rec-lem f g = λ= (⊤ₚ-elim _ idp)

  -- Morphisms of opetopic types

  Map : {ℓ : ULevel} {n : ℕ} (X X' : 𝕆 ℓ n) → Set ℓ 

  frm-map : {ℓ : ULevel} {n : ℕ} {X X' : 𝕆 ℓ n} (g : Map X X') (f : Frm X) → Frm X'

  Map {n = O} X X' = X → X'
  Map {n = S n} (Xₙ , Xₛₙ) (Xₙ' , Xₛₙ') =
    Σ (Map Xₙ Xₙ') λ g →
      (f : Frm Xₙ) → Xₛₙ f → Xₛₙ' (frm-map g f)

  frmₛ-map : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {Xₙ' : 𝕆 ℓ n} {Xₛₙ' : Frm Xₙ' → Set ℓ}
    → (g : Map (Xₙ , Xₛₙ) (Xₙ' , Xₛₙ')) {f : Frm Xₙ} {x : Xₛₙ f}
    → Frmₛ Xₛₙ f x
    → Frmₛ Xₛₙ' (frm-map (fst g) f) (snd g f x)

  frm (frm-map {n = O} g f) = g (frm f)
  pos (frm-map {n = O} g f) = pos f
  typ (frm-map {n = O} g f) = g ∘ typ f
  frm-map {n = S n} (g , η) (f , α , f') = frm-map g f , η f α , frmₛ-map (g , η) f'

  frmₛ-map-η : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} (Xₛₙ : Frm Xₙ → Set ℓ)
    → {Xₙ' : 𝕆 ℓ n} (Xₛₙ' : Frm Xₙ' → Set ℓ)
    → (g : Map (Xₙ , Xₛₙ) (Xₙ' , Xₛₙ')) (f : Frm Xₙ) (x : Xₛₙ f)
    → frmₛ-map g (η-frm f x) == η-frm (frm-map (fst g) f) (snd g f x) 

  frmₛ-map-μ : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {Xₙ' : 𝕆 ℓ n} {Xₛₙ' : Frm Xₙ' → Set ℓ}
    → (g : Map (Xₙ , Xₛₙ) (Xₙ' , Xₛₙ'))
    → {f : Frm Xₙ} {x : Xₛₙ f} (fₛ : Frmₛ Xₛₙ f x)
    → (ϕ : (p : El (pos (opr fₛ))) → Frmₛ Xₛₙ (typ (opr fₛ) p) (dec fₛ p))
    → frmₛ-map g (μ-frm fₛ ϕ) == μ-frm (frmₛ-map g fₛ) λ p → frmₛ-map g (ϕ p)
  
  tree-map : ∀ {ℓ} {n : ℕ} {Xₙ : 𝕆 ℓ n} {Xₛₙ : Frm Xₙ → Set ℓ}
    → {Xₙ' : 𝕆 ℓ n} {Xₛₙ' : Frm Xₙ' → Set ℓ}
    → (g : Map (Xₙ , Xₛₙ) (Xₙ' , Xₛₙ'))
    → {f : Frm (Xₙ , Xₛₙ)} {P : ℙ} {t : El P → Frm (Xₙ , Xₛₙ)}
    → Tree Xₙ Xₛₙ f P t
    → Tree Xₙ' Xₛₙ' (frm-map g f) P (frm-map g ∘ t)
  
  cns-map : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {X' : 𝕆 ℓ n} (g : Map X X')
    → {f : Frm X} {P : ℙ} {t : El P → Frm X}
    → Cns X f P t
    → Cns X' (frm-map g f) P (frm-map g ∘ t)
  cns-map {n = O} g x = x
  cns-map {n = S n} = tree-map

  {-# TERMINATING #-}
  opr-map : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {X' : 𝕆 ℓ n} (g : Map X X') (f : Frm X)
    → Opr X f → Opr X' (frm-map g f)
  pos (opr-map g f x) = pos x
  typ (opr-map g f x) = frm-map g ∘ typ x
  cns (opr-map g f x) = cns-map g (cns x)

  opr (frmₛ-map (g , _) {f} fₛₙ) = opr-map g f (opr fₛₙ)
  dec (frmₛ-map (g , α) fₛₙ) p = α _ (dec fₛₙ p)

  tree-map {Xₙ = Xₙ} {Xₛₙ} {Xₙ'} {Xₛₙ'} (g , α) (lf f x) =
    transport! (λ (f , h) → Tree Xₙ' Xₛₙ' (frm-map g _ , α _ x , f) ⊥ₚ h)
               (pair×= (frmₛ-map-η Xₛₙ Xₛₙ' (g , α) f x) (λ= (⊥ₚ-elim _)))
               (lf (frm-map g f) (α _ x))  
  tree-map {Xₙ = Xₙ} {Xₛₙ} {Xₙ'} {Xₛₙ'} (g , α) (nd x fₛₙ δ ε) =
    let δ' p = frmₛ-map (g , α) (δ p)
        ε' p = opr-map (g , α) (_ , _ , δ p) (ε p)

        pth = ⊔ₚ-Frm-rec-lem
                (⊤ₚ-Frm-rec (_ , x , fₛₙ))
                (Σₚ-Frm-rec (λ p → typ (ε p)))
                (frm-map (g , α))
              ∙ ap (uncurry ⊔ₚ-Frm-rec)
                  (pair×=
                    (⊤ₚ-Frm-rec-lem (_ , x , fₛₙ) (frm-map (g , α)))
                    (Σₚ-Frm-rec-lem (λ p → typ (ε p)) (frm-map (g , α))))
    in transport!
         (λ (f , h) → Tree Xₙ' Xₛₙ' (frm-map g _ , α _ x , f)
                                    (⊤ₚ ⊔ₚ Σₚ (pos (opr fₛₙ))
                                    (λ p → pos (ε p))) h)
         (pair×= (frmₛ-map-μ {Xₛₙ' = Xₛₙ'} (g , α) fₛₙ δ) pth)
         (nd (α _ x) (frmₛ-map (g , α) fₛₙ) δ' ε')

  cns-map-η : ∀ {ℓ} {n : ℕ} {X : 𝕆 ℓ n} {X' : 𝕆 ℓ n} (g : Map X X')
    → (f : Frm X)
    → cns-map g (η-cns f) == η-cns (frm-map g f)
        [ (Cns X' (frm-map g f) ⊤ₚ) ↓ ⊤ₚ-Frm-rec-lem f (frm-map g) ]
  cns-map-η {ℓ} {O} {X} {X'} g f = contr-has-all-paths-↓ ⦃ Lift-preserves-level Unit-level ⦄
  cns-map-η {ℓ} {S n} {X} {X'} (g , gₛ) (f , α , fₛ) =
    let fₛₙ = frmₛ-map (g , gₛ) fₛ
        
        δ p = frmₛ-map (g , gₛ) (η-frm (typ (opr fₛ) p) (dec fₛ p))
        δ' p = η-frm ((frm-map g ∘ typ (opr fₛ)) p) (gₛ (typ (opr fₛ) p) (dec fₛ p))
        
        δ=δ' : δ == δ'
        δ=δ' = λ= λ p → frmₛ-map-η (snd X) (snd X') (g , gₛ) (typ (opr fₛ) p) (dec fₛ p)
        
        ε p = opr-map (g , gₛ) (typ (opr fₛ) p , dec fₛ p , η-frm (typ (opr fₛ) p) (dec fₛ p))
                ⟪ ⊥ₚ , ⊥ₚ-Frm-rec , lf (typ (opr fₛ) p) (dec fₛ p) ⟫ₒₚ
        ε' p = ⟪ ⊥ₚ , ⊥ₚ-Frm-rec , lf ((frm-map g ∘ typ (opr fₛ)) p) (gₛ (typ (opr fₛ) p) (dec fₛ p)) ⟫ₒₚ
        
        ε=ε' : ε == ε' [ (λ δ → (p : El (pos (opr fₛₙ))) → Opr X' (typ (opr fₛₙ) p , dec fₛₙ p , δ p)) ↓ δ=δ' ]
        ε=ε' = ↓-Π-in λ p → {!!}

        foo = apd (λ (δ , ε) → nd (gₛ f α) (frmₛ-map (g , gₛ) fₛ) δ ε) (pair= δ=δ' ε=ε')


    in {!!}

  frmₛ-map-η Xₛₙ {Xₙ'} Xₛₙ' (g , α) f x =
    let pth = ↓-ap-in (uncurry (Cns Xₙ' (frm-map g f))) (⊤ₚ ,_) (cns-map-η g f)
        opr= = Opr=-out (idp , λ= (⊤ₚ-elim _ idp) , pth)
    in Frmₛ=-out (opr= , ↓-Π-in {!!})

  frmₛ-map-μ = {!!}
