structure foo (A B : Type) :=
  (bar : A → Type)
  (baz : B → Type)

instance FunctionA {A B : Type} : has_coe_to_fun (foo A B) :=
{ F   := λ f, A → Type,
  coe := foo.bar }

instance FunctionB {A B : Type} : has_coe_to_fun (foo A B) :=
{ F   := λ f, B → Type,
  coe := foo.baz }

def X : foo unit bool :=
  { bar := λ a, unit,
    baz := λ a, bool }

eval (X ())
eval (X tt)
eval (X ff)
