{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module LowDims where

  module _ (A : Set) where

    UnaryRel : Set₁
    UnaryRel = A → A → Set 

    is-fib-unary : UnaryRel → Set
    is-fib-unary Q = (a₀ : A) → is-contr (Σ A (λ a₁ → Q a₀ a₁))

    data seq (Q : UnaryRel) : A → A → Set where
      emp : {a : A} → seq Q a a
      ext : {a₀ a₁ a₂ : A}
        → (s : seq Q a₀ a₁) (r : Q a₁ a₂) 
        → seq Q a₀ a₂

    SeqRel : UnaryRel → Set₁
    SeqRel Q = {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁ → Set 

    is-fib-seq : {Q : UnaryRel} → SeqRel Q → Set
    is-fib-seq {Q} V = {a₀ a₁ : A} (σ : seq Q a₀ a₁)
      → is-contr (Σ (Q a₀ a₁) (V σ)) 

    --  Showing that a fibrant, unital relation admits a composition
    module _ (Q : UnaryRel) (refl-Q : (a : A) → Q a a) (is-fib-Q : is-fib-unary Q) where

      Q-elim : (a₀ : A) (P : Σ A (Q a₀) → Set)
        → (r : P (a₀ , refl-Q a₀))
        → (x : Σ A (Q a₀)) → P x
      Q-elim a₀ P r x = transport P (contr-has-all-paths ⦃ is-fib-Q a₀ ⦄ (a₀ , refl-Q a₀) x) r 

      Q-elim-β : (a₀ : A) (P : Σ A (Q a₀) → Set)
        → (r : P (a₀ , refl-Q a₀))
        → Q-elim a₀ P r (a₀ , refl-Q a₀) == r
      Q-elim-β a₀ P r = {!!} 

      comp : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁
      comp (emp {a₀}) = refl-Q a₀
      comp (ext {a₀} {a₁} {a₂} s r) = Q-elim a₁ P (idf (Q a₀ a₁)) (a₂ , r) (comp s)

        where P : Σ A (Q a₁) → Set
              P (a , _) = Q a₀ a₁ → Q a₀ a

      comp-unit-l : {a₀ a₁ : A}
        → (q : Q a₀ a₁)
        →  comp (ext emp q) == q
      comp-unit-l {a₀} {a₁} q = Q-elim _ P' u (_ , q) 
        where P' : Σ A (Q a₀) → Set
              P' (a , q) = comp (ext emp q) == q

              P : Σ A (Q a₀) → Set
              P (a , _) = Q a₀ a₀ → Q a₀ a

              u : P' (a₀ , refl-Q a₀)
              u = app= (Q-elim-β a₀ P (idf (Q a₀ a₀))) (refl-Q a₀)

    module _ {Q : UnaryRel} where

      seqcat : {a₀ a₁ a₂ : A} 
        → seq Q a₀ a₁ → seq Q a₁ a₂
        → seq Q a₀ a₂
      seqcat s emp = s
      seqcat s (ext t r) = ext (seqcat s t) r

      seqcat-unit-l : {a₀ a₁ : A} 
        → (s : seq Q a₀ a₁)
        → seqcat emp s == s
      seqcat-unit-l emp = idp
      seqcat-unit-l (ext s r) = ap (λ s → ext s r) (seqcat-unit-l s)

      plc : {a₀ a₁ : A} → seq Q a₀ a₁ → Set
      plc emp = ⊥
      plc (ext s r) = plc s ⊔ ⊤

      src : {a₀ a₁ : A} {s : seq Q a₀ a₁} (p : plc s) → A
      src {s = ext s r} (inl p) = src p
      src {s = ext {a₀} {a₁} {a₂} s r} (inr unit) = a₁

      tgt : {a₀ a₁ : A} {s : seq Q a₀ a₁} (p : plc s) → A
      tgt {s = ext s r} (inl p) = tgt p
      tgt {s = ext {a₀} {a₁} {a₂} s r} (inr unit) = a₂

      inh : {a₀ a₁ : A} {s : seq Q a₀ a₁} (p : plc s) → Q (src p) (tgt p)
      inh {s = ext s r} (inl p) = inh p
      inh {s = ext s r} (inr unit) = r

      μ-seq : {a₀ a₁ : A} (s : seq Q a₀ a₁)
        → (δ : (p : plc s) → seq Q (src p) (tgt p))
        → seq Q a₀ a₁
      μ-seq emp δ = emp
      μ-seq (ext s r) δ =
        seqcat (μ-seq s (λ p → δ (inl p)))
               (δ (inr unit))

      μ-seq-unit : {a₀ a₁ : A} (s : seq Q a₀ a₁)
        → μ-seq s (λ p → ext emp (inh p)) == s
      μ-seq-unit emp = idp
      μ-seq-unit (ext s r) =
        let hyp = μ-seq-unit s
        in ap (λ s → ext s r) hyp

      data tr (R : SeqRel Q) : {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁ → Set where
        lf-tr : {a₀ a₁ : A} (q : Q a₀ a₁)
          → tr R (ext emp q) q
        nd-tr : {a₀ a₁ : A} (s : seq Q a₀ a₁)
          → (δ : (p : plc s) → seq Q (src p) (tgt p))
          → (ε : (p : plc s) → tr R (δ p) (inh p))
          → (q : Q a₀ a₁) (r : R s q)
          → tr R (μ-seq s δ) q

      corolla : (R : SeqRel Q) {a₀ a₁ : A}
        → {σ : seq Q a₀ a₁}
        → {τ : Q a₀ a₁}
        → (r : R σ τ)
        → tr R σ τ
      corolla R {σ = σ} {τ} r  =
        let t = nd-tr {R} σ (λ p → ext emp (inh p)) (λ p → lf-tr (inh p)) τ r
        in transport (λ σ → tr R σ τ) (μ-seq-unit σ) t

      TrRel : SeqRel Q → Set₁
      TrRel R = {a₀ a₁ : A} {s : seq Q a₀ a₁} {q : Q a₀ a₁}
        → tr R s q → R s q → Set

      is-fib-tr : (R : SeqRel Q) (T : TrRel R) → Set
      is-fib-tr R T = {a₀ a₁ : A} {s : seq Q a₀ a₁} {q : Q a₀ a₁}
        → (θ : tr R s q) → is-contr (Σ (R s q) (T θ)) 

    is-refl-unary : UnaryRel → Set
    is-refl-unary Q = (a : A) → Q a a

    is-comp-unary : UnaryRel → Set
    is-comp-unary Q = {a₀ a₁ : A} → seq Q a₀ a₁ → Q a₀ a₁

    is-unital-seqrel : {Q : UnaryRel} → SeqRel Q → Set
    is-unital-seqrel {Q} R = {a₀ a₁ : A} (q : Q a₀ a₁)
      → R (ext emp q) q

    is-vertical-seqrel : {Q : UnaryRel} → is-comp-unary Q → SeqRel Q → Set
    is-vertical-seqrel {Q} comp-Q R = {a₀ a₁ : A}
      → {s t : seq Q a₀ a₁}
      → {u : Q a₀ a₁}
      → R s (comp-Q t)
      → R t u
      → R s u

    is-ext-seqrel : {Q : UnaryRel} → is-comp-unary Q → SeqRel Q → Set
    is-ext-seqrel {Q} comp-Q R = {a₀ a₁ a₂ : A}
          → (s₀ s₀' : seq Q a₀ a₁) (s₁ : seq Q a₁ a₂)
          → (q : Q a₁ a₂)
          → (r : R s₀ (comp-Q s₀')) (r₁ : R s₁ q)
          → R (seqcat s₀ s₁) (comp-Q (ext s₀' q))
    

    module Two (Q : UnaryRel) (is-fib-Q : is-fib-unary Q)
               (R : SeqRel Q) (is-fib-R : is-fib-seq R) where

      refl-Q : is-refl-unary Q
      refl-Q a = fst (contr-center (is-fib-R (emp {Q} {a}))) 

      comp-Q : is-comp-unary Q
      comp-Q = comp Q refl-Q is-fib-Q

      module Three (R-is-unital : is-unital-seqrel R)
                   (R-vertical : is-vertical-seqrel comp-Q R)
                   (R-is-ext : is-ext-seqrel comp-Q R) where
      
        R-loop : (x : A) → R {x} emp (comp-Q emp)
        R-loop x = snd (contr-center (is-fib-R emp))
 
        R-inv : {a₀ a₁ : A} (s : seq Q a₀ a₁)
          → (δ : (p : plc s) → seq Q (src p) (tgt p))
          → (ε : (p : plc s) → R (δ p) (inh p))
          → R (μ-seq s δ) (comp-Q s)
        R-inv emp δ ε = snd (contr-center (is-fib-R emp))
        R-inv (ext s r) δ ε =
          let δ' p = δ (inl p)
              ε' p = ε (inl p)
              
              hyp = R-inv s δ' ε'

          in R-is-ext (μ-seq s (λ p → δ (inl p))) s (δ false) r hyp (ε false)


        assoc : {a₀ a₁ : A}
          → {s : seq Q a₀ a₁} {t : Q a₀ a₁}
          → tr R s t
          → R s t
        assoc (lf-tr q) = R-is-unital q
        assoc (nd-tr s δ ε t r) =
          let r' =  R-inv s δ (λ p → assoc (ε p))
          in  R-vertical  r' r

          -- So, here the idea would be that we can
          -- suppose that t = comp s.  Then we are reduced
          -- to showing that we always have:
          --
          --   R (μ-seq s δ) (comp s)
          --



      module _ (T : TrRel R) (is-fib-T : is-fib-tr R T) where

        -- Yeah, so it's clear you can in fact finish this, though
        -- it needs the fibrancy of T.
        R-is-comp : {a₀ a₁ : A} → (s : seq Q a₀ a₁) → R s (comp-Q s)
        R-is-comp {a₀} {.a₀} emp = snd (contr-center (is-fib-R (emp {Q} {a₀}))) 
        R-is-comp (ext {a₀} {a₁} {a₂} s r) =
          Q-elim Q refl-Q is-fib-Q a₁
            (λ x → R (ext s (snd x)) (comp-Q (ext s (snd x))))
            claim (a₂ , r)

          where by-β : comp-Q (ext s (refl-Q a₁)) == comp-Q s
                by-β = {!Q-elim-β!}

                R-comp : Q a₀ a₁
                R-comp = fst (contr-center (is-fib-R (ext s (refl-Q a₁))))

                R-fill : R (ext s (refl-Q a₁)) R-comp
                R-fill = snd (contr-center (is-fib-R (ext s (refl-Q a₁))))

                by-T-fib : R s R-comp
                by-T-fib = {!!}

                by-ih : R s (comp-Q s)
                by-ih = R-is-comp s 

                thus : comp-Q s == R-comp
                thus = fst= (contr-has-all-paths ⦃ is-fib-R s ⦄ (comp-Q s , by-ih) (R-comp , by-T-fib))
              
                claim : R (ext s (refl-Q a₁)) (comp-Q (ext s (refl-Q a₁)))
                claim = transport! (R (ext s (refl-Q a₁))) (by-β ∙ thus) R-fill

        R-is-unital : is-unital-seqrel R
        R-is-unital q = fst (contr-center (is-fib-T (lf-tr q)))

        R-is-vertical : is-vertical-seqrel comp-Q R
        R-is-vertical {s = s} {t} {u} r r₁  =
          let compt=u : comp-Q t == u
              compt=u = fst= (contr-has-all-paths ⦃ is-fib-R t ⦄ (comp-Q t , R-is-comp t) (u , r₁))
          in transport (R s) compt=u r
          
        R-is-ext : is-ext-seqrel comp-Q R
        R-is-ext {a₀} {a₁} {a₂} s₀ s₀' s₁ q r r₁ =
          let p : comp-Q (ext (ext emp (comp-Q s₀')) q) == comp-Q (ext s₀' q)
              p = ap (Q-elim Q refl-Q is-fib-Q a₁ (λ { (a , _) → Q a₀ a₁ → Q a₀ a }) (idf (Q a₀ a₁)) (a₂ , q))
                     (comp-unit-l Q refl-Q is-fib-Q (comp-Q s₀'))

              t = nd-tr (ext (ext emp (comp-Q s₀')) q)
                         (λ { (inl (inr tt)) → s₀ ; (inr tt) → s₁ })
                         (λ { (inl (inr tt)) → corolla R r ; (inr tt) → corolla R r₁ })
                         (comp-Q (ext s₀' q))
                         (transport (R (ext (ext emp (comp-Q s₀')) q)) p (R-is-comp (ext (ext emp (comp-Q s₀')) q)))
          in fst (contr-center (is-fib-T (transport (λ s → tr R (seqcat s s₁) (comp-Q (ext s₀' q))) (seqcat-unit-l s₀) t)))


        open Three R-is-unital R-is-vertical R-is-ext


        T-is-assoc : {a₀ a₁ : A}
          → {s : seq Q a₀ a₁} {t : Q a₀ a₁}
          → (tr : tr R s t)
          → T tr (assoc tr)
        T-is-assoc (lf-tr q) = snd (contr-center (is-fib-T (lf-tr q)))
        T-is-assoc (nd-tr s δ ε _ r) =
          let hyp p = T-is-assoc (ε p)
          in {!!}

