(* learn more about type classes *)
Require Import CpdtTactics.

Set Implicit Arguments.

Class Category (object: Type) (hom: object -> object -> Type) := {
  identity ( a: object ): hom a a;
  composition { a b c: object }: hom a b -> hom b c -> hom a c;

  leftIdentities { a b: object }( f: hom a b ): composition (identity a) f = f;
  rightIdentities { a b: object }( f: hom a b ): composition f (identity b) = f;
  associativity { a b c d: object }( f: hom a b )( g: hom b c )( h: hom c d ):
    composition (composition f g) h = composition f (composition g h);
}.

Print Category.

Program Definition NaturalsAsCategory: Category (fun (a b: True) => nat) := {|
  identity := fun _ => 0;
  composition := fun _ _ _ f g => f + g;
|}.
Next Obligation.
  crush.
Defined.

Generalizable Variables sourceObject sourceHom targetObject targetHom.

Class Functor `{ source: Category sourceObject sourceHom } `{ target: Category targetObject targetHom } := {
  onObjects: sourceObject -> targetObject;
  onMorphisms { x y: sourceObject }: sourceHom x y -> targetHom (onObjects x) (onObjects y);
  identities( x: sourceObject):
    onMorphisms(identity source x) = target.(identity)(onObjects(x));
  functoriality { x y z: source.(object) }( f: source.(hom)(x)(y) )( g: source.(hom)(y)(z)):
      onMorphisms(source.(composition)(f)(g)) = target.(composition)(onMorphisms(f))(onMorphisms(g))
}.
