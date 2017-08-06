set_option pp.universes true

-- First, we verify everthing works as expected when not parameterised by a universe:
structure X := ( m : Type )

structure Y extends x : X

definition coercion : has_coe Y X :=
  { coe := Y.x }

attribute [instance] coercion

def f ( x : X ) := x.m
def g ( y : Y ) := f y

-- Second, we see something goes wrong when we have explicit universes.
structure {u} pX := ( m : Type u )

structure {u} pY extends x : pX.{u}

definition {u} pcoercion : has_coe pY.{u} pX.{u} :=
  { coe := pY.x }

attribute [instance] pcoercion

def {u} pf ( x : pX.{u} ) := x.m
def {u} pg ( y : pY.{u} ) := pf.{u} y