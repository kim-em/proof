structure X :=
(a : Type) (b : Type)

definition f (x : X) := x^.a
definition g (x : X) := x^.b

/- There are many ways to encode inheritance.
   We can "encode" inheritance using a "parent" field.
   This works well if there are no diamonds.
   Example:
   (D extends C and B,
    B extends A,
    C extends A)

   The encoding used by default in Lean handles diamonds.
   We have a lot of diamonds in the algebraic hierarchy.
 -/
structure Y :=
(parent : X)
(h : f parent -> g parent)

instance Y_to_X : has_coe Y X :=
⟨Y.parent⟩ 

variable y : Y
check f y
check g y

check y^.a  -- Doesn't work, the notation ^. does not take coercions into account
check X.a y -- works

def Y.a (y : Y) : Type := X.a y
def Y.b (y : Y) : Type := X.b y
/- The definitions above are boiler plate code, you can automate their generation
   using meta-programming. -/

check y^.a -- not it works
check y^.b 