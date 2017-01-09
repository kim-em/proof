set_option pp.implicit true

class foo {A : Type} (F : A → A → Type) :=
  (bar : Π {a b : A}, F a b)
  (baz : Π {a b : A}, F a b → F a b)

print foo

