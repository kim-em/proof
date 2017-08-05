structure Category :=
  (Obj : Type)
  (Hom : Obj → Obj → Type)

open Category

inductive path { C : Category } : C.Obj → C.Obj → Type
| nil  : Π ( h : C.Obj ), path h h
| cons : Π { h s t : C.Obj } ( e : C.Hom h s ) ( l : path s t ), path h t