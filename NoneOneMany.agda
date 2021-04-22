{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Algebricity
open import Pb
open import Finitary
open import AlgEqvElim
open import FibEquiv
open import SliceLemmas
open import lib.types.Truncation

module NoneOneMany where

  _|>_ : ∀ {i j} {A : Set i} {B : A → Set j} (x : A) (f : Π A B) → B x
  _|>_ x f = f x 

  infixl 0 _|>_

  pair=-idp-r : ∀ {i j} {A : Set i} {B : Set j} {a₁ a₂ : A} (p : a₁ == a₂)
    → (b : B) → pair= p (↓-cst-in idp) == ap (λ x → (x , b)) p
  pair=-idp-r idp _ = idp

  ↓-cst2-in-r : ∀ {i j} {A B : Set i} {C : A → Set j}
    → {x y : B} (p : x == y)
    → {z t : A} (q : z == t)
    → {u : C z} {v : C t}
    → u == v [ C ↓ q ]
    → u == v [ C ∘ snd ↓ (pair×= p q) ]
  ↓-cst2-in-r idp idp r = r

  
  ↓-Π-cst-app-in' : ∀ {i j} {A : Set i} {B : A → Set j} {C : (x : A) → B x → Set}
    → {u v : Π A B} (h : u == v)
    → {f : (x : A) → C x (u x)}
    → {g : (x : A) → C x (v x)}
    → ((x : A) → f x == g x [ C x ↓ app= h x ])
    → f == g [ (λ h → (x : A) → C x (h x)) ↓ h ]
  ↓-Π-cst-app-in' idp = λ=

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) (M-fin : is-finitary M) where

    open import SliceAlg M M↓ 
    open import SliceUnfold M 
    open ExtUnfold M↓

    module Fibs (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂) (alg-fib : AlgFib M M↓ X₂ is-fib-X₂)
                (X₃ : Rel₃ X₂) (is-fib-X₃ : is-fib₃ X₃) where

      open AlgFib alg-fib

      module X₂-struct = AlgStruct M M↓ (Idx↓ M↓) (↓Rel₁) X₂ is-fib-X₂
      module X₃-struct = AlgStruct ExtSlc₁ ExtSlc↓₁ ↓Rel₁ X₂ X₃ is-fib-X₃

      alg-eqv-to : (i : Idx ExtSlc₂) → Idx↓ ExtSlc↓₂ i → X₂ i 

      module NdLemmas
          (i : Idx M)
          (j : Idx↓ M↓ i) (c : Cns M i)
          (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
          (δ : (p : Pos ExtPlbk₁ {i = i , j} (c , ν))
               → Cns ExtPlbk₁ (Typ ExtPlbk₁ {i = i , j} (c , ν) p))
          (ε : (p : Pos ExtPlbk₁ {i = i , j} (c , ν))
               → Cns ExtSlc₁ (Typ ExtPlbk₁ {i = i , j} (c , ν) p , δ p)) 
          (ϕ : (p : Pos ExtSlc₁ (nd {i = i , j} (c , ν) δ ε))
               → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (nd {i = i , j} (c , ν) δ ε) p)) 
          (c↓ : Cns↓ M↓ j c)
          (ν↓ : (p : Pos M c) → Typ↓ M↓ c↓ p == ν p) 
          (δ↓ : (p : Pos M c) → Cns↓ ExtPlbk↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) p) (δ p)) 
          (ε↓ : (p : Pos M c) → Cns↓ ExtSlc↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) p , δ↓ p) (ε p))
          (ϕ↓ : (p : Pos ExtSlc₁ (nd {i = i , j} (c , ν) δ ε))
                → Typ↓ ExtSlc↓₁ (nd↓ {i↓ = j , idp} (c↓ , ν↓) δ↓ ε↓) p == ϕ p)
          where --(θ↓ : Idx↓ ExtSlc↓₁ ?) where

        open DecPred
        
        ε-has-node : DecPred (Pos M c) 
        P ε-has-node p = is-node (ε p)
        P-is-prop ε-has-node p = Trunc-level
        P-is-dec ε-has-node p = slice-is-dec (ε p)
        
        ε-form : SomeOrNone (Pos M c) ε-has-node
        ε-form = is-fin-disc (Pos M c) (M-fin c) ε-has-node 

        GoalIdx : Idx ExtSlc₂
        GoalIdx = ((((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ) ,
                    ((j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓)) ,
                    nd (c , ν) δ ε , ϕ)
                    
        Goal : Set
        Goal = X₂ GoalIdx

        module IsCorolla (ε-is-lf : (p : Pos M c) → ¬ (is-node (ε p))) where

          CorollaIdx : Idx ExtSlc₂
          CorollaIdx = ((((i , j) , c , ν) , ϕ true) ,
                         η ExtPlbk₂ (((i , j) , c , ν) ,
                         ϕ true))

          CorollaX₂ : X₂ CorollaIdx
          CorollaX₂ = X₃-struct.ηX ((i , j) , c , ν) (ϕ true)

          CorollaX₂-fill : X₃ ((CorollaIdx , CorollaX₂) , _ , _)
          CorollaX₂-fill = X₃-struct.ηX-fill ((i , j) , c , ν) (ϕ true)
          lem : {M : 𝕄} {i : Idx M} {c : Cns M i}
            → (σ : Cnsₛ M (i , c))
            → is-leaf σ
            → η M i == c 
          lem (lf _) p = idp
          lem (nd c δ ε) p = ⊥-elim (p [ true ])

          lem' : {M : 𝕄} {M↓ : 𝕄↓ M} {i : Idx M} {c : Cns M i}
            → (σ : Cnsₛ M (i , c))
            → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
            → Cns↓ₛ M↓ (i↓ , c↓) σ
            → (p : is-leaf σ)
            → η↓ M↓ i↓ == c↓ [ Cns↓ M↓ i↓ ↓ lem σ p ] 
          lem' .(lf _) .(η↓ _ _) (lf↓ _) p = idp
          lem' .(nd _ _ _) .(μ↓ _ c↓ δ↓) (nd↓ c↓ δ↓ ε↓) p = ⊥-elim (p [ true ])

          lem2 : {M : 𝕄} {i : Idx M} {c : Cns M i}
            → (σ : Cnsₛ M (i , c))
            → (p : is-leaf σ)
            → lf i == σ [ (λ c → Cnsₛ M (i , c)) ↓ lem σ p  ]
          lem2 (lf _) p = idp
          lem2 (nd c δ ε) p = ⊥-elim (p [ true ])


          η∼δ : (p : Pos M c) → η ExtPlbk₁ (Typ M c p , ν p) == δ p 
          η∼δ p = lem (ε p) (ε-is-lf p)

          η↓∼δ↓ : (p : Pos M c) → η↓ ExtPlbk↓₁ (Typ↓ M↓ c↓ p , ν↓ p) == δ↓ p [ Cns↓ ExtPlbk↓₁ (Typ↓ M↓ c↓ p , ν↓ p) ↓ η∼δ p ]
          η↓∼δ↓ p = lem' (ε p) (δ↓ p) (ε↓ p) (ε-is-lf p) 
          

          open IdxIh i j c ν δ ε ϕ

          transp-cst=idf' : ∀ {i} {A : Set i} {a x y : A} (p : x == y) (q : x == a)
            → transport (λ x → x == a) p q == (! p) ∙ q
          transp-cst=idf' idp q = idp 

          c=μcδ : c , ν == μ ExtPlbk₁ {i = i , j} (c , ν) δ
          c=μcδ = ap (μ ExtPlbk₁ {i = i , j} (c , ν))
                     (λ= η∼δ)

          lf∼ε : (p : Pos M c) → lf (Typ ExtPlbk₁ {i = i , j} (c , ν) p) == ε p [ (λ c → Cns ExtSlc₁ (_ , c)) ↓ η∼δ p ]
          lf∼ε p = lem2 (ε p) (ε-is-lf p)

          c⇓=μcδ↓ : c↓ , ν↓ == μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓ [ Cns↓ ExtPlbk↓₁ (j , idp)  ↓ c=μcδ ]
          c⇓=μcδ↓ =
            let η↓=δ↓ = ↓-Π-cst-app-in' _ λ p →
                          transport!
                            (λ p → _ == _ [ _ ↓ p ])
                            (app=-β (λ p → lem (ε p) (ε-is-lf p)) p)
                            (lem' (ε p) (δ↓ p) (ε↓ p) (ε-is-lf p))
                       
            in ap↓ (λ δ↓ → μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓) η↓=δ↓
              |> ↓-ap-in (Cns↓ ExtPlbk↓₁ (j , idp)) (μ ExtPlbk₁ {i = i , j} (c , ν)) 


          x = (j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓


          ϕ=x : ϕ true == x [ (λ c → Idx↓ ExtSlc↓₁ ((i , j) , c)) ↓ c=μcδ ]
          ϕ=x =
            let p : c↓ , ν↓ == μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓
                    [ (λ { (c , i↓) → Cns↓ ExtPlbk↓₁ i↓ c}) ↓ pair= c=μcδ (↓-cst-in idp) ]
                p = transport! (λ p → _ == _ [ _ ↓ p ]) (pair=-idp-r c=μcδ (j , idp))
                               (↓-ap-in (λ { (c , i↓) → Cns↓ ExtPlbk↓₁ i↓ c})
                                        (λ x → (x , j , idp))
                                        c⇓=μcδ↓)

            in ! (ϕ↓ true) ∙ᵈ ↓-Σ-in (↓-cst-in idp) p

          target= : ((i , j) , c , ν) , ϕ true == ((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ) , x 
          target= = pair= (pair= idp c=μcδ) (↓-ap-in (Idx↓ ExtSlc↓₁) ((i , j) ,_) ϕ=x)


          foo : ηₛ (Pb M (Idx↓ M↓)) ((i , j) , c , ν) == nd (c , ν) δ ε [ (λ { (δ , _) → Cns ExtSlc₁ (_ , μ ExtPlbk₁ {i = i , j} (c , ν) δ) }) ↓ _ ]
          foo = apd (λ { (δ , ε) → nd {i = i , j} (c , ν) δ ε})
                    (pair= (λ= η∼δ) (↓-Π-cst-app-in' _ λ p → transport! (λ p → _ == _ [ _ ↓ p ]) (app=-β (λ p → η∼δ p) p) (lf∼ε p))) 

          η=nd : ηₛ (Pb M (Idx↓ M↓)) ((i , j) , c , ν) == nd (c , ν) δ ε [ (λ c → Cns ExtSlc₁ ((i , j) , c)) ↓ c=μcδ ]
          η=nd = foo
                 |> ↓-cst2-out (λ= η∼δ) (↓-Π-cst-app-in' _ λ p → transport! (λ p → _ == _ [ _ ↓ p ]) (app=-β (λ p → η∼δ p) p) (lf∼ε p)) 
                 |> ↓-ap-in (λ c → Cns ExtSlc₁ ((i , j) , c)) (μ ExtPlbk₁ {i = i , j} (c , ν))

          foo2 : ηₛ (Pb M (Idx↓ M↓)) ((i , j) , c , ν) == nd (c , ν) δ ε [ ((λ { (i , _) → Cns ExtSlc₁ i })) ↓ target= ]
          foo2 = foo
                 |> ↓-cst2-out (λ= η∼δ) (↓-Π-cst-app-in' _ λ p → transport! (λ p → _ == _ [ _ ↓ p ]) (app=-β (λ p → η∼δ p) p) (lf∼ε p)) 
                 |> ↓-ap-in (Cns ExtSlc₁) (λ δ → ((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ))
                 |> transport (λ x → _ == _ [ _ ↓ x ]) (ap-∘ (λ x → (i , j) , x) (μ ExtPlbk₁ {i = i , j} (c , ν)) (λ= η∼δ)) 
                 |> ↓-cst2-in (pair= idp c=μcδ) (↓-ap-in (Idx↓ ExtSlc↓₁) ((i , j) ,_) ϕ=x) 


          foo3 :  Pos ExtSlc₁ (ηₛ (Pb M (Idx↓ M↓)) ((i , j) , c , ν)) == Pos ExtSlc₁ (nd {i = i , j} (c , ν) δ ε) -- [ (λ c → Set) ↓ c=μcδ  ] 
          foo3 = ↓-cst-out (ap↓ (Pos ExtSlc₁) η=nd)

          η-dec=ϕ : η-dec (Slice (Plbk₁ (Idx↓ M↓))) (Idx↓ ExtSlc↓₁) (ϕ true) == ϕ [ (λ { (i , c) → (p : Pos ExtSlc₁ {i = _ , i} c) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ c p) }) ↓ pair= c=μcδ η=nd ]
          η-dec=ϕ = ↓-Π-in foo70
            where foo70 : {p : Pos ExtSlc₁ (ηₛ (Pb M (Idx↓ M↓)) ((i , j) , c , ν))}
                          {p' : Pos ExtSlc₁ (nd {i = i , j} (c , ν) δ ε)}
                          (q : p == p' [ (λ { (_ , c) → Posₛ (Pb M ↓Rel₀) c }) ↓ pair= c=μcδ η=nd ])
                          → η-dec (Slice (Plbk₁ (Idx↓ M↓))) (Idx↓ ExtSlc↓₁) (ϕ true) p == ϕ p' [ (λ { ((_ , c) , p) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ c p)}) ↓ pair= (pair= c=μcδ η=nd) q ]
                  foo70 {true} {true} q = {!ϕ↓ true!}
                   {- let  foo : {!!}
                        foo = apd↓ {A = Σ (Cns ExtPlbk₁ (i , j)) λ c → Cns ExtSlc₁ ((i , j) , c) }
                                   {B =  λ { (_ , c) → Posₛ (Pb M ↓Rel₀) c }}
                                   {C = λ c p → Idx↓ ExtSlc↓₁ (Typₛ (Pb M ↓Rel₀) (snd c) p)}
                                   (λ {a} b  → ϕ {!transport (Pos)!})
                                   {p = pair= c=μcδ η=nd}
                                   {u = true}
                                   {v = true}
                                   q

                        foo2 : (p : Pos ExtSlc₁ (ηₛ (Pb M (Idx↓ M↓)) ((i , j) , c , ν))) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (ηₛ (Pb M (Idx↓ M↓)) ((i , j) , c , ν)) p)
                        foo2 =  {!cst (ϕ true)!}

                        foo4 : (p : Pos ExtSlc₁ (nd {i = i , j} (c , ν) δ ε)) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (nd {i = i , j} (c , ν) δ ε) p)
                        foo4 = {!!}

                        --foo5 : foo2

                       -- foo4 : ∀ c → (p : Posₛ (Pb M ↓Rel₀)) c → 

                        
                    in {!!} -}
                      where foo100 : ϕ true == ϕ true [ (λ { ((_ , c) , p) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ c p) }) ↓ (pair= (pair= c=μcδ η=nd) q) ]
                            foo100 = apd↓ f q
                              where f : ∀ {c : _} (p : Pos ExtSlc₁ (snd c)) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (snd c) p)
                                    f p = {!!}
                  foo70 {inr (_ , ())}
                  foo70 {true} {inr (p , q)} r = ⊥-elim {P = λ _ → η-dec ExtSlc₁ (Idx↓ ExtSlc↓₁) (ϕ true) true == ϕ (inr (p , q)) [ (λ { ((_ , c) , p) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ c p)}) ↓ pair= (pair= c=μcδ η=nd) r ]} (ε-is-lf p [ q ])

                  foo71 : η-dec (Slice (Plbk₁ (Idx↓ M↓))) (Idx↓ₛ (Pb↓ M↓ ↓Rel₀ (λ i₁ → _==_))) (ϕ true) true == ϕ true
                  foo71 = idp
                  
                  
          source= : ηₛ (Pb M (Idx↓ M↓)) ((i , j) , c , ν) , η-dec (Slice (Plbk₁ (Idx↓ M↓))) (Idx↓ ExtSlc↓₁) (ϕ true) == nd (c , ν) δ ε , ϕ [ Cns ExtPlbk₂ ↓ target= ]
          source= = ↓-Σ-in foo2 {!!}

          corolla= : CorollaIdx == GoalIdx
          corolla= = pair= target= source=

          corolla-case : Goal
          corolla-case = {!!} --transport X₂ corolla= CorollaX₂ 

        module HasDescendent (ε-nd : Trunc ⟨-1⟩ (Σ (Pos M c) (λ p → is-node (ε p)))) where
 {-
          -- Here are the elements we get from the induction hypothesis.
          descendant-ih-idx : (p : Pos M c) → Idx ExtSlc₂
          descendant-ih-idx p = (((Typ M c p , ν p) , δ p) ,
                                  (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p) ,
                                   ε p , λ q → ϕ (inr (p , q)) 

          descendant-ih : (p : Pos M c) → X₂ (descendant-ih-idx p)
          descendant-ih p = alg-eqv-to (descendant-ih-idx p)
            ((((Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p) , idp) , ε↓ p , λ q → ϕ↓ (inr (p , q)))

          --
          --  Arguments to X₃-struct.μX
          --


          

          desc-i : Idx ExtSlc₁
          desc-i = ((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ)

          desc-c : Cns ExtSlc₁ desc-i
          desc-c = X₂-struct.μX-tr i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

          desc-ν : (p : Pos ExtSlc₁ desc-c) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ desc-c p)
          desc-ν = X₂-struct.θX i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

          desc-δ : (p : Pos ExtSlc₁ desc-c) → Cns ExtPlbk₂ (Typ ExtSlc₁ desc-c p , desc-ν p)
          desc-δ true = η ExtSlc₁ ((i , j) , c , ν) , η-dec ExtSlc₁ (Idx↓ ExtSlc↓₁) (ϕ true) 
          desc-δ (inr (p , true)) = ε p , λ q' → ϕ (inr (p , q')) 

          desc-x₀ : Idx↓ ExtSlc↓₁ ((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ)
          desc-x₀ = X₂-struct.μX i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

          desc-x₁ : X₂ ((desc-i , desc-x₀) , desc-c , desc-ν)
          desc-x₁ = X₂-struct.μX-fill i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

          desc-δ↓ : (p : Pos ExtSlc₁ desc-c) → X₂ ((Typ ExtSlc₁ desc-c p , desc-ν p) , desc-δ p)
          desc-δ↓ true = transport! (λ h → X₂ ((((i , j) , c , ν) , h) , desc-δ true ))
                                    (ϕ↓ (inl unit)) (X₃-struct.ηX ((i , j) , c , ν) (ϕ true))
          desc-δ↓ (inr (p , true)) = descendant-ih p


          postulate

            -- The actual definition here takes a super long time to typecheck ...
            descendant-μ : X₂ ((((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ) , desc-x₀) ,
                                    μ ExtPlbk₂ {i = desc-i , desc-x₀} (desc-c , desc-ν) desc-δ)
            -- descendant-μ = X₃-struct.μX desc-i desc-c desc-ν desc-δ
            --                             desc-x₀ desc-x₁ desc-δ↓

            -- This should be true generically because of the form of the substitution.
            -- Question: do we need to use that there is a non-trivial attachment to make this true?
            desc-nd-eq : (nd (c , ν) δ ε , ϕ) == μ ExtPlbk₂ {i = desc-i , desc-x₀} (desc-c , desc-ν) desc-δ

          from-nd-hyp : (j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓ == desc-x₀
          from-nd-hyp = nd-hyp (i , j) (c , ν) δ (j , idp) (c↓ , ν↓) δ↓

          descendant-case : Goal
          descendant-case = transport! (λ h → X₂ ((((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ) , fst h) , snd h))
                                      (pair×= from-nd-hyp desc-nd-eq) descendant-μ 
-}
        goal : Goal
        goal = {!!} -- Coprod-rec HasDescendent.descendant-case
                   --       IsCorolla.corolla-case ε-form

      -- alg-eqv-to : (i : Idx ExtSlc₂) → Idx↓ ExtSlc↓₂ i → X₂ i 
      alg-eqv-to ((((i , j) , ._ , ._) , (.j , idp) , ._ , ._) , lf .(i , j) , ϕ) ((._ , idp) , lf↓ .(j , idp) , ϕ↓) =
        transport! (λ h → X₂ ((iₛ , h) , lf (i , j) , ϕ)) jₛ=jₛ' (snd (contr-center (is-fib-X₂ iₛ (lf (i , j)) ϕ)))

        where iₛ : Idx ExtSlc₁
              iₛ = (i , j) , η M i , η-dec M (Idx↓ M↓) j

              jₛ : Idx↓ ExtSlc↓₁ iₛ
              jₛ = (j , idp) , (η↓ M↓ j , η↓-dec M↓ (λ i j k → j == k) idp)

              jₛ' : Idx↓ ExtSlc↓₁ iₛ
              jₛ' = fst (contr-center (is-fib-X₂ iₛ (lf (i , j)) ϕ))

              jₛ=jₛ' : jₛ == jₛ'
              jₛ=jₛ' = lf-hyp (i , j) (j , idp) ∙
                       -- have to fix the fact that ϕ ≠ ⊥-elim definitionally ...
                       ap (λ h → fst (contr-center (is-fib-X₂ iₛ (lf (i , j)) h))) (λ= (λ { () })) 

      alg-eqv-to ((((i , j) , ._ , ._) , (.j , idp) , a , b) , nd (c , ν) δ ε , ϕ) ((k , idp) , nd↓ (c↓ , ν↓) δ↓ ε↓ , ϕ↓) = goal
        where open NdLemmas i j c ν δ ε ϕ c↓ ν↓ δ↓ ε↓ ϕ↓ 

      postulate
      
        alg-eqv-is-equiv : (i : Idx ExtSlc₂) → is-equiv (alg-eqv-to i)

      alg-eqv : AlgEqv ExtSlc₁ ExtSlc↓₁ X₂ X₃ is-fib-X₃
      AlgEqv.e alg-eqv i = alg-eqv-to i , alg-eqv-is-equiv i
      AlgEqv.η-hyp alg-eqv (i , x) i↓ =
        let foo2 : X₂ ((i , x) , η ExtPlbk₂ (i , x))
            foo2 = alg-eqv-to ((i , x) , η ExtPlbk₂ (i , x)) (i↓ , η↓ ExtPlbk↓₂ i↓)


            foo : alg-eqv-to ((i , x) , η ExtPlbk₂ (i , x)) (i↓ , η↓ ExtPlbk↓₂ i↓) == X₃-struct.ηX i x
            foo = {!idp!}
        in foo
      AlgEqv.μ-hyp alg-eqv i c δ j d δ↓ = {!!}

      -- alg-eqv : AlgEqv ExtSlc₁ ExtSlc↓₁ X₂ X₃ is-fib-X₃
      -- AlgEqv.e alg-eqv i = alg-eqv-to i , alg-eqv-is-equiv i
      -- AlgEqv.η-hyp alg-eqv (((i , j) , c , ν) , (j , idp) , (c↓ , ν↓)) (._ , idp) = {!!}

      --   -- So. The proof here is that when ϕ is instantiated with a constant function
      --   -- at the value give, then the "claim" equality from above evaluates to the
      --   -- identity.  So we have to think about how to set this up as nicely as possible
      --   -- so that this is true.

      --   -- You should check with the given hypotheses that the endpoints are already
      --   -- definitionally equal so that this has a chance of being true ...  but, yeah,
      --   -- that's going to be the idea.

      -- AlgEqv.μ-hyp alg-eqv i σ δ i↓ σ↓ δ↓ = {!!}

