set_option pp.implicit true

class foo {A : Type} :=
  (bar : A)
  (baz : A → A)

print foo
-- attribute [class]
-- structure foo : Π {A : Type}, Type
-- fields:
-- foo.bar : (A : Type) [c : @foo A], A
-- foo.baz : {A : Type} [c : @foo A], A → A

-- I guess the issue here is that since the field baz is a function
-- A → A, the data of what A is contained in the definition of the
-- function (as its domain).
-- This may be somewhat counter-intuitive in our case, but I can think
-- of examples where this would be the desired behaviour. The best
-- solution is probably to define helper functions when this would
-- cause problems.

