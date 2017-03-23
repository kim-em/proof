universe variables u v

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v) 
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)

universe variables u1 v1 u2 v2

structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))

definition CommaCategory { A B C : Category} ( S : Functor A C ) ( T : Functor B C ) : Category :=
{
  Obj      := Σ a : A^.Obj, Σ b : B^.Obj, (C^.Hom (S^.onObjects a) (T^.onObjects b)),
  Hom      := λ p q, subtype (λ gh : (A^.Hom p.1 q.1) × (B^.Hom p.2.1 q.2.1), C^.compose (S^.onMorphisms gh.1) q.2.1 = C^.compose p.2.2 (T^.onMorphisms gh.2) ),
  compose  := sorry
}
