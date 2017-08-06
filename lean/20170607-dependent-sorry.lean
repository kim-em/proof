-- structure F :=
--   (prop : 1 = 1)

-- def parameterized_type : F → Type := sorry
-- def parameterized_prop : Π (x : F), parameterized_type x → Prop := sorry

-- structure C  :=
--   ( f : F )
--   ( p : parameterized_type f )
--   ( q : (parameterized_prop f) p )

-- def test : C := {
--     f := {
--       prop := eq.refl 1
--     },
--     p := sorry,
--     q := sorry
-- }

-- universe u

structure Funct : Type := (prop : true)

def A : Funct → Type := sorry
def B (x : Type) : x → Prop := sorry

structure Cone :=
  ( limit : Funct )
  ( maps  : A limit )
  ( commutativity : B _ maps )

def test : Cone := {
    limit         := ⟨sorry⟩,
    maps          := sorry,
    commutativity := sorry
}