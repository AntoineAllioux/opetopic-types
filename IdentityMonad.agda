{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module IdentityMonad where

  Idxᵢ : Set
  Idxᵢ = ⊤

  Cnsᵢ : Idxᵢ → Set
  Cnsᵢ _ = ⊤

  Posᵢ : {u : Idxᵢ} → Cnsᵢ u → Set
  Posᵢ _ = ⊤

  Typᵢ : {u : Idxᵢ} (c : Cnsᵢ u) → Posᵢ {u = u} c → ⊤
  Typᵢ _ _ = tt

  ηᵢ : (u : Idxᵢ) → Cnsᵢ u
  ηᵢ _ = tt

  η-posᵢ : (u : Idxᵢ) → Posᵢ {u = u} (ηᵢ u)
  η-posᵢ _ = tt
  
  η-pos-elimᵢ : (u : Idxᵢ)
    → (X : (p : Posᵢ {u = u} (ηᵢ u)) → Set)
    → (η-pos* : X (η-posᵢ u))
    → (p : Posᵢ {u = u} (ηᵢ u)) → X p
  η-pos-elimᵢ _ X η-pos* tt = η-pos*
  
  μᵢ : {u : Idxᵢ} (c : Cnsᵢ u)
    → (δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p))
    → Cnsᵢ u
  μᵢ _ δ = δ tt 

  μ-posᵢ : {u : Idxᵢ} (c : Cnsᵢ u)
    → (δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p))
    → (p : Posᵢ {u = u} c) (q : Posᵢ {u = u} (δ p))
    → Posᵢ {u = u} (μᵢ {u = u} c δ)
  μ-posᵢ _ δ _ q = tt

  μ-pos-fstᵢ : {u : Idxᵢ} (c : Cnsᵢ u)
    → (δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p))
    → (p : Posᵢ {u = u} (μᵢ {u = u} c δ)) → Posᵢ {u = u} c
  μ-pos-fstᵢ _ δ p = tt

  μ-pos-sndᵢ : {u : Idxᵢ} (c : Cnsᵢ u)
    → (δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p))
    → (p : Posᵢ {u = u} (μᵢ {u = u} c δ))
    → Posᵢ {u = Typᵢ {u = u} c p} (δ (μ-pos-fstᵢ {u = u} c δ p))
  μ-pos-sndᵢ _ δ p = tt

  postulate

    IdMnd : 𝕄

    Idx-IdMnd : Idx IdMnd ↦ Idxᵢ 
    {-# REWRITE Idx-IdMnd #-}

    Cns-IdMnd : (u : Idxᵢ)
      → Cns IdMnd u ↦ Cnsᵢ u
    {-# REWRITE Cns-IdMnd #-}

    Pos-IdMnd : (u : Idxᵢ) (c : Cnsᵢ u)
      → Pos IdMnd {i = u} c ↦ Posᵢ {u = u} c
    {-# REWRITE Pos-IdMnd #-}

    Typ-IdMnd : (u : Idxᵢ) (c : Cnsᵢ u) (p : Posᵢ {u = u} c)
      → Typ IdMnd {i = u} c p ↦ Typᵢ {u = u} c p
    {-# REWRITE Typ-IdMnd #-}

    η-IdMnd : (u : Idxᵢ) 
      → η IdMnd u ↦ ηᵢ u
    {-# REWRITE η-IdMnd #-}

    η-pos-IdMnd : (u : Idxᵢ)
      → η-pos IdMnd u ↦ η-posᵢ u
    {-# REWRITE η-pos-IdMnd #-}

    η-pos-elim-IdMnd : (u : Idxᵢ)
      → (X : (p : Posᵢ {u = u} (ηᵢ u)) → Set)
      → (η-pos* : X (η-posᵢ u))
      → (p : Posᵢ {u = u} (ηᵢ u)) → X p
      → η-pos-elim IdMnd u X η-pos* p ↦ η-pos-elimᵢ u X η-pos* p
    {-# REWRITE η-pos-elim-IdMnd #-}
    
    μ-IdMnd : {u : Idxᵢ} (c : Cnsᵢ u)
      → (δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p))
      → μ IdMnd {i = u} c δ ↦ μᵢ {u = u} c δ
    {-# REWRITE μ-IdMnd #-}

    μ-pos-IdMnd : {u : Idxᵢ} (c : Cnsᵢ u)
      → (δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p))
      → (p : Posᵢ {u = u} c) (q : Posᵢ {u = Typᵢ {u = u} c p} (δ p))
      → μ-pos IdMnd {i = u} c δ p ↦ μ-posᵢ {u = u} c δ p
    {-# REWRITE μ-pos-IdMnd #-}

    μ-pos-fst-IdMnd : {u : Idxᵢ} (c : Cnsᵢ u)
      → (δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p))
      → (p : Posᵢ {u = u} (μᵢ {u = u} c δ)) 
      → μ-pos-fst IdMnd {i = u} c δ p ↦ μ-pos-fstᵢ {u = u} c δ p
    {-# REWRITE μ-pos-fst-IdMnd #-}

    μ-pos-snd-IdMnd : {u : Idxᵢ} (c : Cnsᵢ u)
      → (δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p))
      → (p : Posᵢ {u = u} (μᵢ {u = u} c δ))
      → μ-pos-snd IdMnd {i = u} c δ p ↦ μ-pos-sndᵢ {u = u} c δ p
    {-# REWRITE μ-pos-snd-IdMnd #-} 



