universe variables u v

class has_compose (Obj : Type u) (Hom : Obj → Obj → Type v) :=
  ( compose : ∀ { X Y Z : Obj } ( f : Hom X Y ) ( g: Hom Y Z ), Hom X Z )
  ( associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h) )

class has_identity (Obj : Type u) (Hom : Obj → Obj → Type v) extends has_compose Obj Hom :=
  ( identity : Π X : Obj, Hom X X )
  ( left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f )
  ( right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity Y) = f )

structure Category (Obj : Type u) (Hom : Obj → Obj → Type v) extends has_identity Obj Hom
