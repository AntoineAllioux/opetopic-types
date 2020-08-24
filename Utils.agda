{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Utils where

  _|>_ : {A : Set} {B : A → Set} → (x : A) → Π A B → B x
  x |> f = f x

  infixl 10 _|>_

  transport↓ : {A : Set} {B : A → Set} (C : {x : A} → B x → Set)
    → {x y : A} (p : x == y)
    → {u : B x} {v : B y} (q : u == v [ B ↓ p ])
    → C u → C v
  transport↓ _ idp idp x = x

  transport↓-! : {A : Set} {B : A → Set} (C : {x : A} → B x → Set)
    → {x y : A} (p : y == x)
    → {u : B x} {v : B y} (q : v == u [ B ↓ p ])
    → C u → C v
  transport↓-! _ idp idp x = x

  transp-↓' : ∀ {i j} {A : Type i} (P : A → Type j) {a₁ a₂ : A}
    → (p : a₁ == a₂) (y : P a₁) → y == transport P p y [ P ↓ p ]
  transp-↓' _ idp _ = idp
