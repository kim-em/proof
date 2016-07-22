(* learn more about type classes *)
Require Import CpdtTactics.
Obligation Tactic := crush.

Generalizable Variables a b c d.

Class Category ( object: Type ) (hom: object -> object -> Type) := {
  identity: forall a, hom a a;
  composition { a b c: object }: hom a b -> hom b c -> hom a c;

  leftIdentities `( f: hom a b ): composition (identity a) f = f;
  rightIdentities `( f: hom a b ): composition f (identity b) = f;
  associativity `( f: hom a b )`( g: hom b c )`( h: hom c d ):
    composition (composition f g) h = composition f (composition g h);
}.

Print Category.

Program Instance NaturalsAsCategory: Category _ (fun (a b: True) => nat) := {|
  identity := fun _ => 0;
  composition := fun _ _ _ f g => f + g;
|}.

Generalizable Variables sourceObject sourceHom targetObject targetHom.

Class Functor `( source: Category(sourceObject)(sourceHom) ) `( target: Category targetObject targetHom ) := {
  onObjects: sourceObject -> targetObject;
  onMorphisms { x y: sourceObject }: sourceHom x y -> targetHom (onObjects x) (onObjects y);
  identities( x: sourceObject ):
    onMorphisms(identity source x) = identity target onObjects x;
  functoriality `( f: hom source x y )( g: hom source y z):
      onMorphisms(source.(composition)(f)(g)) = target.(composition)(onMorphisms(f))(onMorphisms(g))
}.
