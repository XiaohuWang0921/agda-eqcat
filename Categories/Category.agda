{-# OPTIONS --without-K --safe #-}

module Categories.Category where

open import Level
open import Function.Base using (flip; _on_)
open import Data.Product.Base using (_,_)

open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
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
    dom cod  : Arr → Obj
    dom-cong : dom  Preserves _≈₁_ ⟶ _≈₀_
    cod-cong : cod Preserves _≈₁_ ⟶ _≈₀_

  module Eqv₀ = IsEquivalence equiv₀
  module Eqv₁ = IsEquivalence equiv₁

  -- Composable pairs
  Compat : Rel Arr œ
  Compat f g = dom f ≈₀ cod g

  Compat-respˡ-≈ : Compat Respectsˡ _≈₁_
  Compat-respˡ-≈ f = Eqv₀.trans (Eqv₀.sym (dom-cong f))

  Compat-respʳ-≈ : Compat Respectsʳ _≈₁_
  Compat-respʳ-≈ f = flip Eqv₀.trans (cod-cong f)

  Compat-resp-≈ : Compat Respects₂ _≈₁_
  Compat-resp-≈ = Compat-respʳ-≈ , Compat-respˡ-≈

  field
    -- Composition
    comp : ∀ f g → Compat f g → Arr
    comp-cong : ∀ {f g h i} (f≈h : f ≈₁ h) (g≈i : g ≈₁ i) (fg-cpt : Compat f g) (hi-cpt : Compat h i) → comp f g fg-cpt ≈₁ comp h i hi-cpt
    dom-comp : ∀ {f g c} → dom (comp f g c) ≈₀ dom  g
    cod-comp : ∀ {f g c} → cod (comp f g c) ≈₀ cod f

    -- Associativity
    assoc : ∀ {f g h} (fg-cpt : Compat f g) (gh-cpt : Compat g h) → comp (comp f g fg-cpt) h (Eqv₀.trans dom-comp gh-cpt) ≈₁ comp f (comp g h gh-cpt) (Eqv₀.trans fg-cpt (Eqv₀.sym cod-comp))

    -- Identity arrows
    ide : Obj → Arr
    ide-cong : ide Preserves _≈₀_ ⟶ _≈₁_
    dom-ide : ∀ {A} → dom (ide A) ≈₀ A
    cod-ide : ∀ {A} → cod (ide A) ≈₀ A

    -- Composition with identity
    identityˡ : ∀ {f} → comp f (ide (dom f)) (Eqv₀.sym cod-ide) ≈₁ f
    identityʳ : ∀ {f} → comp (ide (cod f)) f dom-ide ≈₁ f

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
      domA : dom arr ≈₀ A
      codB : cod arr ≈₀ B

  open _⇒_ public

  -- Dependent composition
  _∘_ : B ⇒ C → A ⇒ B → A ⇒ C
  (f w/ sf & tf) ∘ (g w/ sg & tg) = comp f g (Eqv₀.trans sf (Eqv₀.sym tg)) w/ Eqv₀.trans dom-comp sg & Eqv₀.trans cod-comp tf

  _≈_ : Rel (A ⇒ B) ℓ
  _≈_ = _≈₁_ on arr

  equiv : IsEquivalence (_≈_ {A} {B})
  equiv = record { refl = refl ; sym = sym ; trans = trans }
    where open Eqv₁

  module Eqv {A B} = IsEquivalence (equiv {A} {B})

  id : A ⇒ A
  id {A} = ide A w/ dom-ide & cod-ide

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
        
        ; dom = cod
        ; cod = dom
        ; dom-cong = cod-cong
        ; cod-cong = dom-cong
        
        ; comp = λ f g eq → comp g f (Eqv₀.sym eq)
        ; comp-cong = λ f≈h g≈i fg-cpt hi-cpt → Eqv₁.sym (comp-cong (Eqv₁.sym g≈i) (Eqv₁.sym f≈h) (Eqv₀.sym hi-cpt) (Eqv₀.sym fg-cpt))
        ; dom-comp = cod-comp
        ; cod-comp = dom-comp
        
        ; assoc = λ fg-cpt gh-cpt → Eqv₁.sym (Eqv₁.trans (comp-cpt-irr (Eqv₀.sym (Eqv₀.trans fg-cpt (Eqv₀.sym dom-comp))) (Eqv₀.trans dom-comp (Eqv₀.sym fg-cpt))) (Eqv₁.trans (assoc (Eqv₀.sym gh-cpt) (Eqv₀.sym fg-cpt)) (comp-cpt-irr (Eqv₀.trans (Eqv₀.sym gh-cpt) (Eqv₀.sym cod-comp)) (Eqv₀.sym (Eqv₀.trans cod-comp gh-cpt)))))
        
        ; ide = ide
        ; ide-cong = ide-cong
        ; dom-ide = cod-ide
        ; cod-ide = dom-ide
        
        ; identityˡ = Eqv₁.trans (comp-cpt-irr (Eqv₀.sym (Eqv₀.sym dom-ide)) dom-ide) identityʳ
        ; identityʳ = identityˡ
        }

  obj-setoid : Setoid o œ
  obj-setoid = record { Carrier = Obj ; _≈_ = _≈₀_ ; isEquivalence = equiv₀ }

  arr-setoid : Setoid m ℓ
  arr-setoid = record { Carrier = Arr ; _≈_ = _≈₁_ ; isEquivalence = equiv₁ }

  hom-setoid : Obj → Obj → Setoid (m ⊔ œ) ℓ
  hom-setoid A B = record { Carrier = A ⇒ B ; _≈_ = _≈_ ; isEquivalence = equiv }

  dom-func cod-func : arr-setoid ⟶ₛ obj-setoid
  dom-func = record { to = dom ; cong = dom-cong }
  cod-func = record { to = cod ; cong = cod-cong }

  ide-func : obj-setoid ⟶ₛ arr-setoid
  ide-func = record { to = ide ; cong = ide-cong }
