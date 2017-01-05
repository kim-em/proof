structure Category :=
  (Obj : Type)
  (Hom : Obj → Obj → Type)

print Category
/-
5:1: structure Category : Type₂
fields:
Category.Obj : Category → Type
Category.Hom : Π (c : Category), Category.Obj c → Category.Obj c → Type
-/

class Category' :=
  (Obj : Type) 
  (Hom : Obj → Obj → Type)

print Category'
/-
17:1: attribute [class]
structure Category' : Type₂
fields:
Category'.Obj : Π [c : Category'], Type
Category'.Hom : Π [c : Category'], Category'.Obj → Category'.Obj → Type
-/
