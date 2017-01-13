set_option pp.implicit true

class foo {A : Type} (F : A → Type) :=
  (bar : Π {a : A}, F a)
  (baz : Π {a : A}, F a → F a)

print foo

-- I guess the issue here is that since the field is a function
-- F a → F a, what exactly F is isn't necessary to know for any given
-- a, the function encodes its domain, and that's all that's
-- necessary. This may be somewhat counter-intuitive in our case, but
-- I can think of examples where this would be the desired
-- behaviour. The best solution is probably to define helper functions
-- when this would cause problems.

