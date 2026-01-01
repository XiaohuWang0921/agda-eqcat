{-# OPTIONS --without-K --safe #-}

module Category where

open import Level
open import Function.Base using (flip; _on_)
open import Data.Product.Base using (_,_)

open import Relation.Binary hiding (_⇒_; Irrelevant)
import Relation.Binary.Reasoning.Setoid as SetoidR

record Category (o œ m ℓ : Level) : Set (suc (o ⊔ œ ⊔ m ⊔ ℓ)) where
  eta-equality
  infix  4 _≈₀_ _≈₁_ _≈_ _⇒_
  infixr 9 _∘_
  
  field
    -- The setoid of objects
    Obj : Set o
    _≈₀_ : Rel Obj œ
    equiv₀ : IsEquivalence _≈₀_

    -- The setoid of morphisms
    Arr : Set m
    _≈₁_ : Rel Arr ℓ
    equiv₁ : IsEquivalence _≈₁_

    -- Source & target functions
    src trgt  : Arr → Obj
    src-cong  : src  Preserves _≈₁_ ⟶ _≈₀_
    trgt-cong : trgt Preserves _≈₁_ ⟶ _≈₀_

  module Eqv₀ = IsEquivalence equiv₀
  module Eqv₁ = IsEquivalence equiv₁

  -- Composable pairs
  Compat : Rel Arr œ
  Compat f g = src f ≈₀ trgt g

  Compat-respˡ-≈ : Compat Respectsˡ _≈₁_
  Compat-respˡ-≈ f = Eqv₀.trans (Eqv₀.sym (src-cong f))

  Compat-respʳ-≈ : Compat Respectsʳ _≈₁_
  Compat-respʳ-≈ f = flip Eqv₀.trans (trgt-cong f)

  Compat-resp-≈ : Compat Respects₂ _≈₁_
  Compat-resp-≈ = Compat-respʳ-≈ , Compat-respˡ-≈

  field
    -- Composition
    comp : ∀ f g → Compat f g → Arr
    comp-cong : ∀ {f g h i} (f≈h : f ≈₁ h) (g≈i : g ≈₁ i) (fg-cpt : Compat f g) (hi-cpt : Compat h i) → comp f g fg-cpt ≈₁ comp h i hi-cpt
    src-comp  : ∀ {f g c} → src  (comp f g c) ≈₀ src  g
    trgt-comp : ∀ {f g c} → trgt (comp f g c) ≈₀ trgt f

    -- Associativity
    assoc : ∀ {f g h} (fg-cpt : Compat f g) (gh-cpt : Compat g h) → comp (comp f g fg-cpt) h (Eqv₀.trans src-comp gh-cpt) ≈₁ comp f (comp g h gh-cpt) (Eqv₀.trans fg-cpt (Eqv₀.sym trgt-comp))

    -- Identity arrows
    ide : Obj → Arr
    ide-cong : ide Preserves _≈₀_ ⟶ _≈₁_
    src-ide  : ∀ {A} → src  (ide A) ≈₀ A
    trgt-ide : ∀ {A} → trgt (ide A) ≈₀ A

    -- Composition with identity
    identityˡ : ∀ {f} → comp f (ide (src f)) (Eqv₀.sym trgt-ide) ≈₁ f
    identityʳ : ∀ {f} → comp (ide (trgt f)) f src-ide ≈₁ f

  comp-cpt-irr : ∀ {f g} (cpt cpt′ : Compat f g) → comp f g cpt ≈₁ comp f g cpt′
  comp-cpt-irr = comp-cong Eqv₁.refl Eqv₁.refl

  private
    variable
      A B C : Obj

  -- Hom-family indexed by objects
  record _⇒_ (A B : Obj) : Set (m ⊔ œ) where
    eta-equality
    constructor _w/_&_
    field
      arr : Arr
      srcA  : src  arr ≈₀ A
      trgtB : trgt arr ≈₀ B

  open _⇒_ public

  -- Dependent composition
  _∘_ : B ⇒ C → A ⇒ B → A ⇒ C
  (f w/ sf & tf) ∘ (g w/ sg & tg) = comp f g (Eqv₀.trans sf (Eqv₀.sym tg)) w/ Eqv₀.trans src-comp sg & Eqv₀.trans trgt-comp tf

  _≈_ : Rel (A ⇒ B) ℓ
  _≈_ = _≈₁_ on arr

  equiv : IsEquivalence (_≈_ {A} {B})
  equiv = record { refl = refl ; sym = sym ; trans = trans }
    where open Eqv₁

  module Eqv {A B} = IsEquivalence (equiv {A} {B})

  id : A ⇒ A
  id {A} = ide A w/ src-ide & trgt-ide

  ∘-cong : (_∘_ {B} {C} {A}) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ∘-cong {_} {_} {_} {f w/ sf & tf} {h w/ sh & th} {g w/ sg & tg} {i w/ si & ti} f≈h g≈i = comp-cong f≈h g≈i (Eqv₀.trans sf (Eqv₀.sym tg)) (Eqv₀.trans sh (Eqv₀.sym ti))

  op : Category o œ m ℓ
  op = record
        { Obj = Obj
        ; _≈₀_ = _≈₀_
        ; equiv₀ = equiv₀
        
        ; Arr = Arr
        ; _≈₁_ = _≈₁_
        ; equiv₁ = equiv₁
        
        ; src = trgt
        ; trgt = src
        ; src-cong = trgt-cong
        ; trgt-cong = src-cong
        
        ; comp = λ f g eq → comp g f (Eqv₀.sym eq)
        ; comp-cong = λ f≈h g≈i fg-cpt hi-cpt → Eqv₁.sym (comp-cong (Eqv₁.sym g≈i) (Eqv₁.sym f≈h) (Eqv₀.sym hi-cpt) (Eqv₀.sym fg-cpt))
        ; src-comp = trgt-comp
        ; trgt-comp = src-comp
        
        ; assoc = λ fg-cpt gh-cpt → Eqv₁.sym (Eqv₁.trans (comp-cpt-irr (Eqv₀.sym (Eqv₀.trans fg-cpt (Eqv₀.sym src-comp))) (Eqv₀.trans src-comp (Eqv₀.sym fg-cpt))) (Eqv₁.trans (assoc (Eqv₀.sym gh-cpt) (Eqv₀.sym fg-cpt)) (comp-cpt-irr (Eqv₀.trans (Eqv₀.sym gh-cpt) (Eqv₀.sym trgt-comp)) (Eqv₀.sym (Eqv₀.trans trgt-comp gh-cpt)))))
        
        ; ide = ide
        ; ide-cong = ide-cong
        ; src-ide = trgt-ide
        ; trgt-ide = src-ide
        
        ; identityˡ = Eqv₁.trans (comp-cpt-irr (Eqv₀.sym (Eqv₀.sym src-ide)) src-ide) identityʳ
        ; identityʳ = identityˡ
        }

  obj-setoid : Setoid o œ
  obj-setoid = record { Carrier = Obj ; _≈_ = _≈₀_ ; isEquivalence = equiv₀ }

  arr-setoid : Setoid m ℓ
  arr-setoid = record { Carrier = Arr ; _≈_ = _≈₁_ ; isEquivalence = equiv₁ }

  hom-setoid : Obj → Obj → Setoid (m ⊔ œ) ℓ
  hom-setoid A B = record { Carrier = A ⇒ B ; _≈_ = _≈_ ; isEquivalence = equiv }
