module HoleFilling where

data Bool : Set where
  true : Bool
  false : Bool

∧ : Bool -> Bool -> Bool
∧ true true = true
∧ false true = false
∧ true false = false
∧ false false = false
