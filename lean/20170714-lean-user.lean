def ℤ₀ := ℕ × ℕ

def eqv : ℤ₀ → ℤ₀ → Prop
| (a, b) (c, d) := a + d = c + b

infix ` ∽ `:50 := eqv

-- Definition 4.1.2.
def add_ℤ₀ : ℤ₀ → ℤ₀ → ℤ₀
| (a, b) (c, d) := (a + c, b + d) 

-- Lemma 4.1.3 (Addition and multiplication are well-defined).

private theorem add_ℤ₀.respects_eqv : ∀ {a b a' b'}, a ∽ a' → b ∽ b' → add_ℤ₀ a b ∽ add_ℤ₀ a' b'
| (a₁, a₂) (b₁, b₂) (a'₁, a'₂) (b'₁, b'₂) :=
  assume a_eqv_a' b_eqv_b',
  have h₁ : a₁ + a'₂ = a'₁ + a₂, from a_eqv_a',
  have h₂ : b₁ + b'₂ = b'₁ + b₂, from b_eqv_b',
  have h₃ : a₁ + b₁ + a'₂ + b'₂ = a'₁ + b'₁ + a₂ + b₂, from 
    calc
      a₁ + b₁ + a'₂ + b'₂ = a₁ + a'₂ + b₁ + b'₂ : by simp [add_comm]
                      ... = a₁ + a'₂ + b'₁ + b₂ : by simp [add_assoc, h₂^.symm]
                      ... = a'₁ + a₂ + b'₁ + b₂ : by simp [add_assoc, h₁^.symm]
                      ... = a'₁ + b'₁ + a₂ + b₂ : by simp [add_comm],
  have h₄ : (a₁ + b₁, a₂ + b₂) ∽ (a'₁ + b'₁, a'₂ + b'₂), from h₃, -- Why does this fail?
  have h₅ : add_ℤ₀ (a₁, a₂) (b₁, b₂) = (a₁ + b₁, a₂ + b₂), from rfl,
  have h₆ : add_ℤ₀ (a'₁, a'₂) (b'₁, b'₂) = (a'₁ + b'₁, a'₂ + b'₂), from rfl,
  show add_ℤ₀ (a₁, a₂) (b₁, b₂) ∽ add_ℤ₀ (a'₁, a'₂) (b'₁, b'₂), from sorry