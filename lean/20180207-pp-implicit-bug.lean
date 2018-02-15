set_option pp.implicit true

structure C := 
  ( d : Π { X : Type }, list X → list X )

def P(c : C):= c.d [0]

#print P

def P : C → list ℕ :=
λ (c : C), c.d ℕ [0]

def P : C → list ℕ :=
λ (c : C), @C.d c ℕ [0]