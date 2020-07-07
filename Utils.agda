{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Utils where

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
