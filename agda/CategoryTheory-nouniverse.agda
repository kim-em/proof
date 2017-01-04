module CategoryTheory-nouniverse where

open import Relation.Binary
open import Relation.Binary.Flip
open import Relation.Binary.PropositionalEquality

open import Agda.Builtin.Unit
open import Data.Nat
open import Data.Nat.Properties.Simple

open import Level renaming (zero to lzero ; suc to lsuc ; _⊔_ to _l⊔_)

--open import Agda.Primitive

record Category : Set₁ where
  infixr 9 _∘_

  field
    Obj : Set
    Hom : Rel Obj lzero

    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    identityL  : ∀ {A B} → (f : Hom A B) → id ∘ f ≡ f
    identityR  : ∀ {A B} → (f : Hom A B) → f ∘ id ≡ f
    assoc      : ∀ {A B C D} → (f : Hom C D) → (g : Hom B C)
                   → (h : Hom A B) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)


ℕasCategory : Category
ℕasCategory = record
  { Obj = ⊤
  ; Hom = λ _ _ → ℕ
  ; id  = 0
  ; _∘_ = _+_

  ; identityL = λ f → refl        -- Auto-solved!
  ; identityR = +-right-identity  -- ¬ auto-solved.
  ; assoc = +-assoc  -- This was tough: the order had to be
                     -- exactly the same as above; ¬ auto-solved.
  }

record Functor {o₁ o₂ ℓ₁ ℓ₂}
         : Set (lsuc (o₁ l⊔ o₂ l⊔ ℓ₁ l⊔ ℓ₂)) where
  open Category
  field 
    {source} : Category {o₁} {ℓ₁}
    {target} : Category {o₂} {ℓ₂}
    onObj : Obj source → Obj target
    onMor : ∀ {A B} → Hom source A B
              → Hom target (onObj A) (onObj B)

    --identities : ∀ {A} → onMor (d {A})
                  -- → onMor (id {A}) ≡ id {onObj A}
