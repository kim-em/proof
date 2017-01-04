module CategoryTheory where

open import Relation.Binary
open import Relation.Binary.Flip
open import Relation.Binary.PropositionalEquality

open import Agda.Builtin.Unit
open import Data.Nat
open import Data.Nat.Properties.Simple

open import Level renaming (suc to lsuc ; _⊔_ to _l⊔_)

--open import Agda.Primitive

record Category {o ℓ} : Set (lsuc (o l⊔ ℓ)) where
  infixr 9 _∘_

  field
    Obj : Set o
    Hom : Rel Obj ℓ

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
         : Set (lsuc (o₁ l⊔ ℓ₁) l⊔ (lsuc (o₂ l⊔ ℓ₂))) where
--  --open Category {_ _}
--
  field 
    {source} : Category {o₁} {ℓ₁}
    {target} : Category {o₂} {ℓ₂}
    onObj : Category.Obj source → Category.Obj target
    onMor : ∀ {A B} → Category.Hom source A B
              → Category.Hom target (onObj A) (onObj B)

--    identities : ∀ {A}
--                   → onMor (Category.id {o₁ ℓ₁} {A}) ≡ Category.id {o₂ ℓ₂} {onObj A}

