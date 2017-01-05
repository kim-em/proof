Require Import CpdtTactics.
Set Implicit Arguments.

Module Type Category.
  Parameter object: Type.
  Parameter hom: object -> object -> Type.
  Parameter composition:
    forall a b c: object,
      hom(a)(b) -> hom(b)(c) -> hom(a)(c).

  Axiom associativity:
    forall a b c d: object,
    forall f: hom(a)(b),
    forall g: hom(b)(c),
    forall h: hom(c)(d),
      composition(composition(f)(g))(h) = composition(f)(composition(g)(h)).
End Category.

Module NaturalsAsCategory: Category.
  Definition object := True.
(*  Sadly, type inference doesn't work as well in Modules *)
(*  Definition hom a b := nat. *)
  Definition hom(a b: True) := nat.
  Definition composition := fun ( _ _ _: True ) ( f g: nat ) => f + g.
  (* and this is horrifically verbose *)
  Program Definition associativity:
    forall a b c d: True,
    forall f: hom(a)(b),
    forall g: hom(b)(c),
    forall h: hom(c)(d),
      composition(a)(c)(d)(composition(a)(b)(c)(f)(g))(h) = composition(a)(b)(d)(f)(composition(b)(c)(d)(g)(h)).
    crush.
  Defined.
End NaturalsAsCategory.