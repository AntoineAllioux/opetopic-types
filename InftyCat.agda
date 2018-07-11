{-# OPTIONS --without-K --rewriting --verbose=plymnd:10 #-}

open import HoTT
open import StrictPoly
open import OpetopicTypes

module InftyCat where

  -- Right, this should be an ∞PreCat .....
  -- Below you add the completeness ...
  ∞Cat : Type₁
  ∞Cat = Σ Type₀ (λ Ob → ∞Alg (slc (pb (id ⊤) (λ { unit → Ob }))))

  module _ (C : ∞Cat) where

    Ob = fst C
    Alg = snd C
    Mor = carrier Alg

    Hom : Ob → Ob → Type₀
    Hom x y = Ops Mor ((unit , y) , (unit , cst x))

    comp-seq : Ob → Ob → Type₀
    comp-seq x y = niche Mor ((unit , y) , unit , cst x)

    one-seq : {x y : Ob} → Hom x y → comp-seq x y
    one-seq {x} {y} f = box (unit , y) (unit , cst x)
                            (λ { unit → unit , λ { unit → x }})
                            (λ { unit → dot (unit , x) }) ,
                          (λ { (inl unit) → f ; (inr (unit , ())) })

    two-seq : {x y z : Ob} → Hom y z → Hom x y → comp-seq x z 
    two-seq {x} {y} {z} f g = box (unit , z) (unit , λ { unit → y }) (λ { unit → unit , λ { unit → x }})
                                  (λ { unit → box (unit , y) (unit , λ { unit → x }) (λ { unit → unit , λ { unit → x }})
                                  (λ { unit → dot (unit , x) })}) ,
                                    λ { (inl unit) → f ;
                                        (inr (unit , inl unit)) → g ;
                                        (inr (unit , inr (unit , ()))) }

    Hom₂ : (x y : Ob) (s : comp-seq x y) (t : Hom x y) → Type₀
    Hom₂ x y s t = Ops (Rels Mor) ((((unit , y) , unit , cst x) , t) , s)

    comp-tree : (x y : Ob) (s : comp-seq x y) (t : Hom x y) → Type₀
    comp-tree x y s t = niche (Rels Mor) ((((unit , y) , unit , cst x) , t) , s)

    -- Okay, we want to make a simplex.
    simplex : (x y z : Ob)
      → (f : Hom x y) (g : Hom y z) (h : Hom x z)
      → (α : Hom₂ x z (two-seq g f) h)
      → comp-tree x z (two-seq g f) h
    simplex x y z f g h α =
      (box (((unit , z) , unit , cst x) , h)
        (two-seq g f)
        (λ { (inl unit) → one-seq g ;
             (inr (unit , inl unit)) → one-seq f ;
             (inr (unit , inr ())) })  -- These should be the individual arrows as single sequences ...
        (λ { (inl unit) → dot {M = (pb (slc (pb (id ⊤) (λ { unit → fst C }))) (Ops Mor))} (((unit , z) , unit , cst y) , g) ;
             (inr (unit , inl unit)) → dot {M = (pb (slc (pb (id ⊤) (λ { unit → fst C }))) (Ops Mor))} (((unit , y) , unit , cst x) , f) ;
             (inr (unit , inr ())) })) ,
        {!!}  


    -- The type of witnesses that f ∘ g = h 
  --   is-comp : {x y z : Ob} → Hom y z → Hom x y → Hom x z → Type₀
  --   is-comp {x} {y} {z} f g h = Ops (Rels Mor) ((((unit , z) , unit , cst x) , h) ,
  --                                                (comp-niche f g))

  --   comp : {x y z : Ob} → Hom y z → Hom x y → Hom x z
  --   comp f g = filler-of (comp-niche f g) (is-alg Alg) 

  --   comp-is-comp : {x y z : Ob} (f : Hom y z) (g : Hom x y) → 
  --                  is-comp f g (comp f g)
  --   comp-is-comp f g = witness-of (comp-niche f g) (is-alg Alg)                   

  --   id-niche : (x : Ob) → niche Mor ((unit , x) , unit , cst x)
  --   id-niche x = (dot (unit , x)) , λ { () }

  --   ident : (x : Ob) → Hom x x
  --   ident x = filler-of (id-niche x) (is-alg Alg)

  --   -- Idea is obvious: draw the 2-pasting diagram with two loops
  --   -- and the witness for the identity composed with itself.
  --   -- It's composite is a filler for the empty niche.  Since the
  --   -- space of fillers is contractible, it is equal to the identity.
  --   -- End of proof.
  --   -- id-comp-id : (x : Ob) → is-comp (ident x) (ident x) (ident x)
  --   -- id-comp-id x = {!!}

  --     -- where bubble-niche : niche (Rels Mor) ((((unit , x) , unit , cst x) , comp (ident x) (ident x)) ,
  --     --                                         (dot (unit , x)) , λ { () })
  --     --       bubble-niche = (box (((unit , x) , (unit , (cst x))) , (comp (ident x) (ident x)))
  --     --                       (comp-niche (ident x) (ident x))
  --     --                         (λ { (inl unit) → {!!} ;
  --     --                              (inr (unit , inl unit)) → {!!} ;
  --     --                              (inr (unit , inr (unit , snd₁))) → {!!} })
  --     --                         (λ { (inl unit) → box (((unit , x) , ((unit , cst x))) , (ident x)) (id-niche x) _ (λ { () }) ;               --  The first loop
  --     --                              (inr (unit , inl unit)) → box (((unit , x) , ((unit , cst x))) , (ident x)) (id-niche x) _ (λ { () }) ;  --  The second loop
  --     --                              (inr (unit , inr (unit , ()))) })) ,

  --     --         λ { p → {!p!} } -- Here go the decorations by witnesses!

  -- --   record is-h-equiv {x y : Ob} (f : Hom x y) : Type₀ where
  -- --     field
  -- --       g₀ : Hom y x
  -- --       g₀-inv : is-comp f g₀ (ident y)
  -- --       g₁ : Hom y x
  -- --       g₁-inv : is-comp g₁ f (ident x)

  -- --   h-equiv : (x y : Ob) → Type₀
  -- --   h-equiv x y = Σ (Hom x y) (λ f → is-h-equiv f)




  --   -- unit-left-niche : {x y : Ob} (f : Hom x y) → niche Rels
  --   --   ((((unit , y) , (unit , cst x)) , f) ,
  --   --   (η-slc (pb (id ⊤) (λ { unit → fst C })) ((unit , y) , unit , cst x)) ,
  --   --   λ { (inl unit) → f ; (inr (_ , ())) })
  --   -- unit-left-niche {x} {y} f =
  --   --   (box ((box {i = unit , y} (unit , cst x) _ (λ { unit → box (unit , cst x) _ (λ { unit → dot (unit , x) }) })) ,
  --   --     λ { (inl unit) → f ;
  --   --         (inr (unit , inl unit)) → ident x ;
  --   --         (inr (unit , inr (unit , ()))) })
  --   --    {!!} {!!}) , {!!}



    
