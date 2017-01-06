section bundled
  structure Category_bundled :=
    (Obj : Type)
    (Hom : Obj → Obj → Type)

  open Category_bundled

  structure Functor_bundled (source target: Category_bundled) :=
    (onObjects: Obj source -> Obj target)
    (onMorphisms: Π { A B : Obj source }, Hom source A B -> Hom target (onObjects A) (onObjects B))
end bundled

section parameterized
  structure Category_parameterized
    (Obj : Type)
    (Hom : Obj → Obj → Type)

  structure Functor_parameterized
    { Obj1 : Type } { Hom1 : Obj1 -> Obj1 -> Type } ( source : Category_parameterized Obj1 Hom1 )
    { Obj2 : Type } { Hom2 : Obj2 -> Obj2 -> Type } ( target : Category_parameterized Obj2 Hom2 ) :=
    (onObjects: Obj1 -> Obj2 )
    (onMorphisms: Π { A B : Obj1 }, Hom1 A B -> Hom2 (onObjects A) (onObjects B))
end parameterized

section bundled_class
  class Category_bundled_class :=
    (Obj : Type)
    (Hom : Obj → Obj → Type)

  open Category_bundled_class

  structure Functor_bundled_class (source target: Category_bundled_class) :=
    (onObjects: @Obj source -> @Obj target)
    (onMorphisms: Π { A B : @Obj source }, @Hom source A B -> @Hom target (onObjects A) (onObjects B))
end bundled_class

section parameterized_class
  class Category_parameterized_class
    (Obj : Type)
    (Hom : Obj → Obj → Type)

  structure Functor_parameterized_class
    { Obj1 : Type } { Hom1 : Obj1 -> Obj1 -> Type } ( source : Category_parameterized_class Obj1 Hom1 )
    { Obj2 : Type } { Hom2 : Obj2 -> Obj2 -> Type } ( target : Category_parameterized_class Obj2 Hom2 ) :=
    (onObjects: Obj1 -> Obj2 )
    (onMorphisms: Π { A B : Obj1 }, Hom1 A B -> Hom2 (onObjects A) (onObjects B))
end parameterized_class
