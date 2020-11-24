{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FundamentalThm where

  -- The fundamental theorem of HoTT
  
  fundamental-thm : ∀ {i} (A : Type i) (P : A → Type i)
    → (a₀ : A) (r : P a₀) (is-c : is-contr (Σ A P))
    → (a₁ : A) → P a₁ ≃ (a₀ == a₁)
  fundamental-thm A P a₀ r is-c a₁ = equiv to from to-from from-to 

    where to :  P a₁ → a₀ == a₁
          to p = fst= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p))

          from : a₀ == a₁ → P a₁
          from p = transport P p r

          to-from : (p : a₀ == a₁) → to (from p) == p
          to-from idp = ap fst= claim

            where claim : contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r) == idp
                  claim = contr-has-all-paths ⦃ =-preserves-contr {x = (a₀ , r)} {y = a₀ , r} is-c ⦄
                            (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₀ , r)) idp

          from-to : (p : P a₁) → from (to p) == p
          from-to p = to-transp (snd= (contr-has-all-paths ⦃ is-c ⦄ (a₀ , r) (a₁ , p)))

  --
  --  A couple coherences for later
  --

  rotate-left-eqv : ∀ {i} {A : Set i} {a₀ a₁ a₂ : A}
    → (p : a₀ == a₁) (q : a₁ == a₂) (r : a₀ == a₂)
    → (p ∙ q == r) ≃ (q == ! p ∙ r)
  rotate-left-eqv idp q r = ide (q == r)

  postulate
  
    rotate-right-eqv : ∀ {i} {A : Set i} {a₀ a₁ a₂ : A}
      → (p : a₀ == a₁) (q : a₁ == a₂) (r : a₀ == a₂)
      → (p ∙ q == r) ≃ (p == r ∙ ! q)

  --
  --  Higher dimensional generalizations
  --

  module _ {A : Set} where

    BinRel : Set₁
    BinRel = A → A → Set

    is-fib-bin-rel : BinRel → Set
    is-fib-bin-rel B = (a : A) → is-contr (Σ A (B a))

    eq-is-fib : is-fib-bin-rel _==_
    eq-is-fib a = has-level-in ((a , idp) , contr) 

      where contr : (p : Σ A (_==_ a)) → (a , idp) == p
            contr (a , idp) = idp
            
    --
    --  Dimension 1 
    --
    
    data _===_ : A → A → Set where
      emp : {a : A} → a === a
      ext : {a₀ a₁ a₂ : A} → a₀ == a₁ → a₁ === a₂ → a₀ === a₂

    SeqRel : Set₁
    SeqRel = {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁ → Set 

    is-fib-seq-rel : (R : SeqRel) → Set
    is-fib-seq-rel R = {a₀ a₁ : A} (σ : a₀ === a₁)
      → is-contr (Σ (a₀ == a₁) (R σ)) 

    -- The composition relation
    comp : {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁
    comp emp = idp
    comp (ext p σ) = p ∙ comp σ

    CompRel : SeqRel
    CompRel σ τ = comp σ == τ 

    seqcat : {a₀ a₁ a₂ : A} → a₀ === a₁ → a₁ === a₂ → a₀ === a₂
    seqcat emp σ₁ = σ₁
    seqcat (ext p σ₀) σ₁ = ext p (seqcat σ₀ σ₁)

    postulate 
      seqcat-unit-r-rew : {a₀ a₁ : A}
        → {σ : a₀ === a₁}
        → seqcat σ emp ↦ σ
      {-# REWRITE seqcat-unit-r-rew #-}

    seqcat-unit-r : {a₀ a₁ : A} (σ : a₀ === a₁)
      → seqcat σ emp == σ
    seqcat-unit-r emp = idp
    seqcat-unit-r (ext x σ) =
      ap (ext x) (seqcat-unit-r σ)

    comp-seqcat : {a₀ a₁ a₂ : A}
      → (σ₀ : a₀ === a₁) (σ₁ : a₁ === a₂)
      → comp (seqcat σ₀ σ₁) == comp σ₀ ∙ comp σ₁
    comp-seqcat emp σ₁ = idp
    comp-seqcat (ext p σ₀) σ₁ =
      ap (λ x → p ∙ x) (comp-seqcat σ₀ σ₁) ∙
      ! (∙-assoc p (comp σ₀) (comp σ₁))

  
    is-unital-rel : SeqRel → Set
    is-unital-rel R = (a : A) → R emp (idp {a = a}) 

    div : {a₀ a₁ a₂ : A} (σ : a₁ === a₂) (τ : a₀ == a₂) → a₀ == a₁
    div σ τ = τ ∙ ! (comp σ) 

    is-divisible : SeqRel → Set
    is-divisible R = {a₀ a₁ a₂ : A} (p : a₀ == a₁)
      → (σ : a₁ === a₂) (τ : a₀ == a₂)
      → R (ext p σ) τ ≃ (p == div σ τ)

    comp-divisible : is-divisible CompRel
    comp-divisible p σ τ = goal

      where goal : (p ∙ comp σ == τ) ≃ (p == τ ∙ ! (comp σ) )
            goal = rotate-right-eqv p (comp σ) τ 

    comp-unique : (R : SeqRel) (ϕ : is-fib-seq-rel R)
      → (ψ : is-unital-rel R) (ρ : is-divisible R)
      → {a₀ a₁ : A} (σ : a₀ === a₁) (τ : a₀ == a₁)
      → R σ τ ≃ (comp σ == τ)
    comp-unique R ϕ ψ ρ {a} emp τ =
      fundamental-thm (a == a) (λ p → R emp p) idp (ψ a) (ϕ emp) τ
    comp-unique R ϕ ψ ρ (ext p σ) τ =
      (comp-divisible p σ τ) ⁻¹ ∘e (ρ p σ τ)
      
    --
    --  Dimension 2
    -- 

    plc : {a₀ a₁ : A} → a₀ === a₁ → Set
    plc emp = ⊥
    plc (ext _ σ) = ⊤ ⊔ plc σ

    src : {a₀ a₁ : A} {σ : a₀ === a₁} (p : plc σ) → A
    src {σ = ext {a₀} _ _} (inl unit) = a₀
    src {σ = ext {a₀} _ σ} (inr p) = src p

    tgt : {a₀ a₁ : A} {σ : a₀ === a₁} (p : plc σ) → A
    tgt {σ = ext {a₁ = a₁} _ _} (inl unit) = a₁
    tgt {σ = ext _ _} (inr p) = tgt p

    inh : {a₀ a₁ : A} {σ : a₀ === a₁} (p : plc σ) → src p == tgt p
    inh {σ = ext x _} (inl unit) = x
    inh {σ = ext _ σ} (inr p) = inh p

    seqcat-plc-l : {a₀ a₁ a₂ : A}
      → (σ : a₀ === a₁) (σ₁ : a₁ === a₂)
      → plc σ
      → plc (seqcat σ σ₁)
    seqcat-plc-l (ext x₁ σ) σ₁ (inl tt) = inl tt
    seqcat-plc-l (ext x₁ σ) σ₁ (inr p) = inr (seqcat-plc-l σ σ₁ p)

    seqcat-plc-r : {a₀ a₁ a₂ : A}
      → (σ : a₀ === a₁) (σ₁ : a₁ === a₂)
      → plc σ₁
      → plc (seqcat σ σ₁)
    seqcat-plc-r emp σ₁ p = p
    seqcat-plc-r (ext x₁ σ) σ₁ p = inr (seqcat-plc-r σ σ₁ p)

    μ-seq : {a₀ a₁ : A} (σ : a₀ === a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → a₀ === a₁
    μ-seq emp δ = emp
    μ-seq (ext _ σ) δ =
      seqcat (δ (inl unit))
             (μ-seq σ (λ p → δ (inr p)))

    postulate
        μ-seq-η : {a₀ a₁ : A}
          → (σ : a₀ === a₁)
          → μ-seq σ (λ p → ext (inh p) emp) ↦ σ
        {-# REWRITE μ-seq-η #-}

    data tr (R : SeqRel) : {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁ → Set where
      lf-tr : {a₀ a₁ : A} (p : a₀ == a₁)
        → tr R (ext p emp) p
      nd-tr : {a₀ a₁ : A}
        → (σ : a₀ === a₁) (τ : a₀ == a₁)
        → (r : R σ τ)
        → (δ : (p : plc σ) → src p === tgt p)
        → (ε : (p : plc σ) → tr R (δ p) (inh p))
        → tr R (μ-seq σ δ) τ 

    corolla : {R : SeqRel} {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      → R σ τ
      → tr R σ τ
    corolla {σ = σ} {τ} θ = nd-tr σ τ θ (λ p → ext (inh p) emp) λ p → lf-tr (inh p) 

    TrRel : SeqRel → Set₁
    TrRel R = {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      → tr R σ τ → R σ τ → Set 

    is-fib-tr-rel : (R : SeqRel) (S : TrRel R) → Set
    is-fib-tr-rel R T = {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr R σ τ) → is-contr (Σ (R σ τ) (T θ)) 

    -- The associative relation
    comp-μ : {a₀ a₁ : A} (σ : a₀ === a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → comp (δ p) == (inh p))
      → comp (μ-seq σ δ) == comp σ
    comp-μ emp δ ε = idp
    comp-μ (ext p σ) δ ε = 
      let δ' p = δ (inr p)
          ε' p = ε (inr p)
          σ' = μ-seq σ δ'
      in comp-seqcat (δ true) σ' ∙ ε true ∙2 comp-μ σ δ' ε'

    assoc : {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr CompRel σ τ)
      → comp σ == τ
    assoc (lf-tr τ) = ∙-unit-r τ
    assoc (nd-tr σ τ θ δ ε) =
      comp-μ σ δ (λ p → assoc (ε p)) ∙ θ

    AssocRel : TrRel CompRel
    AssocRel θ ζ = assoc θ == ζ 

    is-unital-tr-rel : (T : TrRel CompRel) → Set
    is-unital-tr-rel T = {a₀ a₁ : A}
      → (p : a₀ == a₁)
      → T (lf-tr p) (∙-unit-r p)

    tr-div : {a₀ a₁ : A}
      → (σ : a₀ === a₁) (τ : a₀ == a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → tr CompRel (δ p) (inh p))
      → (ζ : comp (μ-seq σ δ) == τ)
      → comp σ == τ
    tr-div σ τ δ ε ζ = ! (comp-μ σ δ (λ p → assoc (ε p))) ∙ ζ 

    record is-div-rel (R : SeqRel) (T : TrRel R) : Set where
      field
        div' : {a₀ a₁ : A}
          → (σ : a₀ === a₁) (τ : a₀ == a₁)
          → (δ : (p : plc σ) → src p === tgt p)
          → (ε : (p : plc σ) → tr R (δ p) (inh p))
          → (ζ : R (μ-seq σ δ) τ) 
          → R σ τ
 
        fill' : {a₀ a₁ : A}
          → (σ : a₀ === a₁) (τ : a₀ == a₁)
          → (θ : R σ τ)
          → (δ : (p : plc σ) → src p === tgt p)
          → (ε : (p : plc σ) → tr R (δ p) (inh p))
          → (ζ : R (μ-seq σ δ) τ) 
          → T (nd-tr σ τ (div' σ τ δ ε ζ) δ ε) ζ ≃ (θ == div' σ τ δ ε ζ)
          
    open is-div-rel

    is-tr-div-rel : (R : SeqRel) → Set
    is-tr-div-rel R = {a₀ a₁ : A}
      → (σ : a₀ === a₁) (τ : a₀ == a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → tr R (δ p) (inh p))
      → (ζ : R (μ-seq σ δ) τ) 
      → R σ τ

    is-divisible-tr-rel : (T : TrRel CompRel) → Set
    is-divisible-tr-rel T = {a₀ a₁ : A}
      → (σ : a₀ === a₁) (τ : a₀ == a₁)
      → (θ : comp σ == τ)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → tr CompRel (δ p) (inh p))
      → (ζ : comp (μ-seq σ δ) == τ)
      → T (nd-tr σ τ θ δ ε) ζ ≃ (θ == tr-div σ τ δ ε ζ) 

    is-divisible-tr-rel' : (R : SeqRel) (T : TrRel R) → Set
    is-divisible-tr-rel' R T = {a₀ a₁ : A}
      → (σ : a₀ === a₁) (τ : a₀ == a₁)
      → (δ : (p : plc σ) → src p === tgt p)
      → (ε : (p : plc σ) → tr R (δ p) (inh p))
      → (ζ : R (μ-seq σ δ) τ)
      → is-contr (Σ (R σ τ) λ θ → T (nd-tr σ τ θ δ ε) ζ)
    
    assoc-is-divisible : is-divisible-tr-rel AssocRel 
    assoc-is-divisible σ τ θ δ ε ζ = goal

      where goal : (comp-μ σ δ (λ p → assoc (ε p)) ∙ θ == ζ) ≃ 
                   (θ == ! (comp-μ σ δ (λ p → assoc (ε p))) ∙ ζ)
            goal = rotate-left-eqv (comp-μ σ δ (λ p → assoc (ε p))) θ ζ
            
    assoc-unique : (T : TrRel CompRel) (ϕ : is-fib-tr-rel CompRel T)
      → (ψ : is-unital-tr-rel T) (ρ : is-divisible-tr-rel T)
      → {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (θ : tr CompRel σ τ) (ζ : comp σ == τ)
      → T θ ζ ≃ AssocRel θ ζ
    assoc-unique T ϕ ψ ρ (lf-tr τ) ζ =
      fundamental-thm (τ ∙ idp == τ) (T (lf-tr τ)) (∙-unit-r τ) (ψ τ) (ϕ (lf-tr τ)) ζ
    assoc-unique T ϕ ψ ρ (nd-tr σ τ θ δ ε) ζ =
      (assoc-is-divisible σ τ θ δ ε ζ) ⁻¹ ∘e (ρ σ τ θ δ ε ζ)

    pos : {R : SeqRel} {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → tr R σ τ
      → Set
    pos (lf-tr _) = ⊥
    pos (nd-tr σ _ r δ ε) = ⊤ ⊔ Σ (plc σ) λ p → pos (ε p) 

    ss2 : {R : SeqRel} {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → {α : tr R σ τ}
      → pos α
      → A
    ss2 {a₀ = a₀} {α = nd-tr σ _ r δ ε} (inl tt) = a₀
    ss2 {α = nd-tr σ _ r δ ε} (inr (p , q)) = ss2 q

    tt2 : {R : SeqRel} {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → {α : tr R σ τ}
      → pos α
      → A
    tt2 {a₁ = a₁} {α = nd-tr σ _ r δ ε} (inl tt) = a₁
    tt2 {α = nd-tr σ _ r δ ε} (inr (p , q)) = tt2 q

    s2 : {R : SeqRel} {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → {α : tr R σ τ}
      → (p : pos α)
      → ss2 p === tt2 p
    s2 {α = nd-tr σ _ r δ ε} (inl tt) = σ
    s2 {α = nd-tr σ _ r δ ε} (inr (p , q)) = s2 q

    t2 : {R : SeqRel} {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → {α : tr R σ τ}
      → (p : pos α)
      → ss2 p == tt2 p
    t2 {α = nd-tr σ τ r δ ε} (inl tt) = τ
    t2 {α = nd-tr σ τ r δ ε} (inr (p , q)) = t2 q

    μ-seq-plc : {a₀ a₁ : A}
      → (σ : a₀ === a₁)
      → (ϕ : (p : plc σ) → src p === tgt p)
      → (p : plc σ) (q : plc (ϕ p))
      → plc (μ-seq σ ϕ)
    μ-seq-plc (ext x σ) ϕ (inl tt) q = seqcat-plc-l _ _ q
    μ-seq-plc (ext x σ) ϕ (inr p) q =
      seqcat-plc-r (ϕ (inl tt))
                   (μ-seq σ (λ p → ϕ (inr p)))
                   (μ-seq-plc σ (λ p → ϕ (inr p)) p q)
      

    inh2 : {R : SeqRel} {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → {α : tr R σ τ}
      → (p : pos α)
      → R (s2 p) (t2 p)
    inh2 {α = nd-tr σ τ r δ ε} (inl tt) = r
    inh2 {α = nd-tr σ τ r δ ε} (inr (p , q)) = inh2 q

    postulate
      src-μ-seq-plc : {a₀ a₁ : A}
        → (σ : a₀ === a₁)
        → (ϕ : (p : plc σ) → src p === tgt p)
        → (p : plc σ) (q : plc (ϕ p))
        → src (μ-seq-plc σ ϕ p q) ↦ src q
      {-# REWRITE src-μ-seq-plc #-}

      tgt-μ-seq-plc : {a₀ a₁ : A}
        → (σ : a₀ === a₁)
        → (ϕ : (p : plc σ) → src p === tgt p)
        → (p : plc σ) (q : plc (ϕ p))
        → tgt (μ-seq-plc σ ϕ p q) ↦ tgt q
      {-# REWRITE tgt-μ-seq-plc #-}

      inh-μ-seq-plc : {a₀ a₁ : A}
        → (σ : a₀ === a₁)
        → (ϕ : (p : plc σ) → src p === tgt p)
        → (p : plc σ) (q : plc (ϕ p))
        → inh (μ-seq-plc σ ϕ p q) ↦ inh q
      {-# REWRITE inh-μ-seq-plc #-}

      μ-seq-plc-unit-r : {a₀ a₁ : A}
        → (σ : a₀ === a₁)
        → (p : plc σ) (q : plc (ext (inh p) emp))
        → μ-seq-plc σ (λ p → ext (inh p) emp) p q ↦ p
      {-# REWRITE μ-seq-plc-unit-r #-}

      μ-seq-assoc : {a₀ a₁ : A}
        → {σ : a₀ === a₁}
        → (ϕ : (p : plc σ) → src p === tgt p)
        → (ψ : (p : plc (μ-seq σ ϕ)) → src p === tgt p)
        → μ-seq (μ-seq σ ϕ) ψ ↦ μ-seq σ (λ p → μ-seq (ϕ p) λ q → ψ (μ-seq-plc σ ϕ p q))
      {-# REWRITE μ-seq-assoc #-}

    γ-tr : {R : SeqRel} {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (α : tr R σ τ)
      → (ϕ : (p : plc σ) → src p === tgt p)
      → (ψ : (p : plc σ) → tr R (ϕ p) (inh p))
      → tr R (μ-seq σ ϕ) τ
    γ-tr (lf-tr _) ϕ ψ = ψ (inl tt)
    γ-tr (nd-tr σ _ r δ ε) ϕ ψ =
      let ϕ' p q = ϕ (μ-seq-plc σ δ p q)
          ψ' p q = ψ (μ-seq-plc σ δ p q)
          δ' p = μ-seq (δ p) (ϕ' p)
          ε' p = γ-tr (ε p) (ϕ' p) (ψ' p)
      in nd-tr _ _ r δ' ε'

    μ-tr : {R : SeqRel} {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → (α : tr R σ τ)
      → (δ : (p : pos α) → tr R (s2 p) (t2 p))
      → tr R σ τ
    μ-tr (lf-tr _) δ = lf-tr _
    μ-tr (nd-tr σ _ r δ₁ ε) δ =
      let δ' p q = δ (inr (p , q))
          ψ p = μ-tr (ε p) (δ' p)
      in γ-tr (δ (inl tt)) δ₁ ψ

    postulate
      μ-tr-unit-r : {R : SeqRel} {a₀ a₁ : A}
        → {σ : a₀ === a₁} {τ : a₀ == a₁}
        → (α : tr R σ τ)
        → μ-tr α (λ p → corolla (inh2 p)) ↦ α
      {-# REWRITE μ-tr-unit-r #-}

    data tr2 (R : SeqRel) (T : TrRel R) : {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → tr R σ τ
      → R σ τ
      → Set where
      
      lf-tr2 : {a₀ a₁ : A}
        → {σ : a₀ === a₁} {τ : a₀ == a₁}
        → (ρ : R σ τ)
        → tr2 R T (corolla ρ) ρ -- (ext p emp) p
        
      nd-tr2 : {a₀ a₁ : A}
        → {σ : a₀ === a₁} {τ : a₀ == a₁}
        → (α : tr R σ τ)
        → (ρ : R σ τ)
        → (r : T α ρ)
        → (δ : (p : pos α) → tr R (s2 p) (t2 p))
        → (ε : (p : pos α) → tr2 R T (δ p) (inh2 p))
        → tr2 R T (μ-tr α δ) ρ

    corolla2 : {R : SeqRel} {T : TrRel R} {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → {α : tr R σ τ}
      → {ρ : R σ τ}
      → (r : T α ρ)
      → tr2 R T α ρ
    corolla2 {α = α} {ρ} r = nd-tr2 α ρ r (λ p → corolla (inh2 p)) (λ p → lf-tr2 (inh2 p))

    Tr2Rel : (R : SeqRel) (T : TrRel R) → Set₁
    Tr2Rel R T = {a₀ a₁ : A}
        → {σ : a₀ === a₁} {τ : a₀ == a₁}
        → {α : tr R σ τ}
        → {ρ : R σ τ}
        → tr2 R T α ρ → T α ρ → Set

    is-fib-tr-rel2 : (R : SeqRel) (S : TrRel R) (T : Tr2Rel R S) → Set
    is-fib-tr-rel2 R S' T = {a₀ a₁ : A}
      → {σ : a₀ === a₁} {τ : a₀ == a₁}
      → {θ : tr R σ τ} {ρ : R σ τ}
      → (α : tr2 R S' θ ρ)
      → is-contr (Σ (S' θ ρ) (T α)) 
    

    module _ (R : SeqRel) (S : TrRel R) (T : Tr2Rel R S)
             (is-fib-R : is-fib-seq-rel R)
             (is-fib-S : is-fib-tr-rel R S)
             (is-fib-T : is-fib-tr-rel2 R S T) where



      -- postulate
      
      --   thm : {!!}
      --     → {a₀ a₁ : A} (σ : a₀ === a₁) (τ : a₀ == a₁)
      --     → R σ τ ≃ CompRel σ τ 



      completeness : Set
      completeness = {a₀ a₁ a₂ : A}
        → (p : a₀ == a₁) (q : a₀ == a₂)
        → ((a₁ , p) == (a₂ , q)) ≃ Σ (a₁ == a₂) (λ r → R (ext p (ext r emp)) q)

      emp-tr : {a : A} (p : a == a) (r : R emp p) → tr R emp p
      emp-tr p r = nd-tr emp p r (λ { () }) (λ { () })

      -- So, is there a map in one direction or the other?
      completeness-map : (is-unital-R : is-unital-rel R)
        → (is-divisible-R : is-tr-div-rel R)
        → {a₀ a₁ a₂ : A}
        → (p : a₀ == a₁) (q : a₀ == a₂)
        → ((a₁ , p) == (a₂ , q)) → Σ (a₁ == a₂) (λ r → R (ext p (ext r emp)) q)
      completeness-map is-u-R is-d-R p .p idp =
        let
            --comp :  → R {!!}
            bar = {!!}
            ρ : R (ext p emp) p
            ρ = fst (contr-center (is-fib-S (lf-tr p)))
            tr : tr R (ext p (ext idp emp)) p
            tr = nd-tr (ext p (ext idp emp)) p {!!} {!!} {!!}
            --tr2 : tr R (ext p (ext idp emp)) p
            --tr2 = ?
            foo : R (ext p (ext idp emp)) p
            foo = is-d-R _ _ ((λ { true → ext p emp ;
                               (inr true) → emp })) (λ { true → lf-tr p ;
                              (inr true) → emp-tr idp (is-u-R _) }) ρ -- fst (contr-center (is-fib-S tr))
        in idp , foo -- fst (contr-center (is-fib-S tr))
      

      

      -- Wow, this I find at least somewhat surprising, but okay.
      completeness-inv : (is-u-R : is-unital-rel R)
        → {a₀ a₁ a₂ : A}
        → (p : a₀ == a₁) (q : a₀ == a₂)
        → Σ (a₁ == a₂) (λ r → R (ext p (ext r emp)) q) → ((a₁ , p) == (a₂ , q))
      completeness-inv is-u-R {a₁ = a₁} p q (idp , r) = pair= idp (fst= (contr-has-all-paths ⦃ is-fib-R (ext p emp) ⦄ (p , blorp) (q , bleep)))

        where blorp : R (ext p emp) p
              blorp = fst (contr-center (is-fib-S (lf-tr p)))  

              bleep : R (ext p emp) q
              bleep = fst (contr-center (is-fib-S (nd-tr (ext p (ext idp emp)) q r
                          (λ { true → ext p emp ;
                               (inr true) → emp })
                          λ { true → lf-tr p ;
                              (inr true) → emp-tr idp (is-u-R a₁) }))) 

      -- Now, if we assume completeness, I think I can prove that R
      -- has left liftings.  On the other hand, it looks like if I
      -- knew that *S* has left liftings, then I would actually be
      -- able to prove completeness.  Not sure what to make of that....

      -- On the other hand, can I now just prove directly that R agrees
      -- with composition?

      thm : (is-u-R : is-unital-rel R)
        → (is-div : is-div-rel R S)
        → {a₀ a₁ : A} (σ : a₀ === a₁) (τ : a₀ == a₁)
        → R σ τ ≃ CompRel σ τ 
      thm is-u-R is-d {a₀} emp τ = {!!}  -- This is fundamental theorem non-sense
      thm is-u-R is-d (ext idp σ) τ = comp-case

        where R-tr : R (ext idp σ) τ → tr R σ τ
              R-tr r =             
                     (nd-tr (ext idp σ) τ r
                             (λ { true → emp ; 
                                  (inr p) → ext (inh p) emp })
                             λ { true → emp-tr idp (is-u-R _) ;
                                 (inr p) → lf-tr (inh p) })

              suffices-to : R (ext idp σ) τ → R σ τ 
              suffices-to r = fst (contr-center (is-fib-S (R-tr r)))

              suffices-from : R σ τ → R (ext idp σ) τ
              suffices-from r = div' is-d (ext idp σ) τ
                                       (λ { true → emp ; (inr p) → ext (inh p) emp })
                                       (λ { true → emp-tr idp (is-u-R _) ; (inr p) → lf-tr (inh p) })
                                       r
              
              suffices : R (ext idp σ) τ ≃ R σ τ 
              suffices = suffices-to , is-eq _ suffices-from to-from from-to
                where to-from : suffices-to ∘ suffices-from ∼ idf _
                      to-from x = fst= (contr-has-all-paths ⦃ is-fib-S (R-tr (suffices-from x)) ⦄
                                         (y , snd (contr-center (is-fib-S (R-tr (suffices-from x)))))
                                         (x , {!<– (fill' is-d _ _ _ _ _ _) idp!}))
                        where y : R σ τ
                              y = suffices-to (suffices-from x)


                      from-to : suffices-from ∘ suffices-to ∼ idf _
                      from-to x = ! p
                        where fill : S (R-tr x) (suffices-to x)
                              fill = snd (contr-center (is-fib-S (R-tr x)))

                              p : x == suffices-from (suffices-to x)
                              p = –> (fill' is-d _ _ _ _ _ _) {!fill!} --fill

              
              comp-case : R (ext idp σ) τ ≃ (comp σ == τ)
              comp-case = (thm is-u-R is-d σ τ) ∘e suffices 

      -- Okay, it's a bit annoying because of some non-computation, but
      -- it seems that this is going to work fine, yeah? Oh one direction
      -- will just use the unit, but the other will use either completeness
      -- or else the lifting property of S.  Which, by the way, suggests that
      -- these two properties are equivalent.

      -- Hmm. Okay.  So while it's true that this will work, it won't
      -- generalize: in the next dimension, you won't be able to just
      -- compose with this nullifying tree to get what you want.


      -- -- is-fib-bin-rel : BinRel → Set
      -- -- is-fib-bin-rel B = (a : A) → is-contr (Σ A (B a))

      -- -- data tr (R : SeqRel) : {a₀ a₁ : A} → a₀ === a₁ → a₀ == a₁ → Set where
      -- --   lf-tr : {a₀ a₁ : A} (p : a₀ == a₁)
      -- --     → tr R (ext p emp) p
      -- --   nd-tr : {a₀ a₁ : A}
      -- --     → (σ : a₀ === a₁) (τ : a₀ == a₁)
      -- --     → (r : R σ τ)
      -- --     → (δ : (p : plc σ) → src p === tgt p)
      -- --     → (ε : (p : plc σ) → tr R (δ p) (inh p))
      -- --     → tr R (μ-seq σ δ) τ 

      -- -- TrRel : SeqRel → Set₁
      -- -- TrRel R = {a₀ a₁ : A} {σ : a₀ === a₁} {τ : a₀ == a₁}
      -- --   → tr R σ τ → R σ τ → Set 

      -- -- is-fib-seq-rel : (R : SeqRel) → Set
      -- -- is-fib-seq-rel R = {a₀ a₁ : A} (σ : a₀ === a₁)
      -- --   → is-contr (Σ (a₀ == a₁) (R σ)) 

      -- -- is-unital-rel : SeqRel → Set
      -- -- is-unital-rel R = (a : A) → R emp (idp {a = a}) 

      -- -- div : {a₀ a₁ a₂ : A} (σ : a₁ === a₂) (τ : a₀ == a₂) → a₀ == a₁
      -- -- div σ τ = τ ∙ ! (comp σ) 

      -- -- is-divisible : SeqRel → Set
      -- -- is-divisible R = {a₀ a₁ a₂ : A} (p : a₀ == a₁)
      -- --   → (σ : a₁ === a₂) (τ : a₀ == a₂)
      -- --   → R (ext p σ) τ ≃ (p == div σ τ)

      ⊤⊔⊥-elim : (X : ⊤ ⊔ ⊥ → Set) (u : X true) (p : ⊤ ⊔ ⊥) → X p
      ⊤⊔⊥-elim X u true = u

      is-complete : Set
      is-complete = {a₀ a₁ : A}
        → (σ : a₀ === a₁)
        → (τ τ₁ : a₀ == a₁)
        → (α : R σ τ) (α₁ : R σ τ₁)
        → ((τ , α) == (τ₁ , α₁))
          ≃ Σ (R (ext τ emp) τ₁) (λ β →
               S (nd-tr (ext τ emp) τ₁ β (⊤⊔⊥-elim _ σ) (⊤⊔⊥-elim _ (corolla α)))
                 α₁) --  (transport (λ σ → R σ τ₁) (! (seqcat-unit-r σ)) α₁))       

      is-complete-is-divisible : is-complete → is-divisible-tr-rel' R S 
      is-complete-is-divisible cmpl σ τ δ ε ζ = has-level-in (ctr , {!!})
        where σ-comp = fst (contr-center (is-fib-R σ))

              σ-fill : R σ σ-comp
              σ-fill = snd (contr-center (is-fib-R σ))

              α : R (μ-seq σ δ) σ-comp
              α = fst (contr-center (is-fib-S (nd-tr _ _ σ-fill δ ε)))

              β : R (ext σ-comp emp) τ
              β = fst (–> (cmpl (μ-seq σ δ) σ-comp τ α ζ) (contr-has-all-paths ⦃ is-fib-R _ ⦄ _ _))

              β-fill : S (nd-tr _ _ β _ _) ζ
              β-fill = snd (–> (cmpl (μ-seq σ δ) σ-comp τ α ζ) (contr-has-all-paths ⦃ is-fib-R _ ⦄ _ _))

              δ' = λ { true → σ  }
              ε' = λ { true → corolla σ-fill }

              θ : R σ τ
              θ = fst (contr-center (is-fib-S (nd-tr (ext σ-comp emp) τ β δ' ε')))

              θ-fill : S (nd-tr _ _ β δ' ε') θ
              θ-fill = snd (contr-center (is-fib-S (nd-tr (ext σ-comp emp) τ β δ' ε')))

              ζ₁ : R (μ-seq σ δ) τ
              ζ₁ = fst (contr-center (is-fib-S (nd-tr σ τ θ δ ε)))

              ζ₁-fill : S (nd-tr σ τ θ δ ε) ζ₁
              ζ₁-fill = snd (contr-center (is-fib-S (nd-tr σ τ θ δ ε)))

              tree : tr R (μ-seq σ δ) τ 
              tree = nd-tr (ext σ-comp emp) τ β (λ { true → μ-seq σ δ}) λ { true → nd-tr σ σ-comp σ-fill δ ε }

              tree2 = nd-tr2 {R} {S} (nd-tr (ext σ-comp emp) τ β _ _) ζ β-fill
                                            (λ { true → corolla β ; (inr (inl tt , inl tt)) → nd-tr σ σ-comp σ-fill δ ε })
                                            (λ { true → lf-tr2 β ; (inr (inl tt , inl tt)) → corolla2 (snd (contr-center (is-fib-S (nd-tr _ _ σ-fill δ ε)))) })

              tree2-comp = fst (contr-center (is-fib-T tree2))

              tree3 = nd-tr2 {R} {S} (nd-tr σ τ _ δ ε) ζ₁ ζ₁-fill (λ { true → nd-tr _ _ β δ' ε' ; (inr (p , q)) → corolla (inh2 q) })
                                                                   λ { true → corolla2  θ-fill ; (inr (p , q)) → lf-tr2 (inh2 q) }

              tree3-comp = fst (contr-center (is-fib-T tree3))
              

              ζ₁=ζ : ζ₁ , {!tree3-comp!} == ζ , tree2-comp
              ζ₁=ζ = contr-has-all-paths ⦃ is-fib-S _ ⦄ _ _ 

                                                    
              ctr : Σ (R σ τ) (λ θ₁ → S (nd-tr σ τ θ₁ δ ε) ζ)
              ctr = θ , transport (S (nd-tr σ τ θ δ ε)) (fst= ζ₁=ζ) ζ₁-fill
              
              pth : (y : Σ (R σ τ) (λ θ₁ → S (nd-tr σ τ θ₁ δ ε) ζ)) → ctr == y
              pth (θ' , θ'-fill) =
                let θ=θ' : (θ , {!!}) == (θ' , {!!})
                    θ=θ' = contr-has-all-paths ⦃ {!!} ⦄ _ _
                in {!!}


      is-divisible-is-complete : is-divisible-tr-rel' R S → is-complete
      is-divisible-is-complete div σ τ τ₁ α α₁ = f , is-eq f {!!} {!!} {!!}
        where f : τ , α == τ₁ , α₁
                → Σ (R (ext τ emp) τ₁) (λ β →
                     S (nd-tr (ext τ emp) τ₁ β (⊤⊔⊥-elim _ σ) (⊤⊔⊥-elim _ (corolla α)))
                        α₁)
              f p = contr-center (div (ext τ emp) τ₁ (⊤⊔⊥-elim _ σ) (⊤⊔⊥-elim _ (corolla α)) α₁)

              g : Σ (R (ext τ emp) τ₁) (λ β →
                     S (nd-tr (ext τ emp) τ₁ β (⊤⊔⊥-elim _ σ) (⊤⊔⊥-elim _ (corolla α)))
                        α₁)
                  → τ , α == τ₁ , α₁
              g (r , s) = {!!}
