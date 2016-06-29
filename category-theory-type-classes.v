(* learn more about type classes *)

Class Category { object: Type } { hom: object -> object -> Type } : Type := {
  identity: forall a: object, hom(a)(a);
  composition { a b c: object }:
      hom(a)(b) -> hom(b)(c) -> hom(a)(c);
  leftIdentities { a b: object }( f: hom(a)(b) ): composition(identity(a))(f) = f;
  rightIdentities { a b: object }( f: hom(a)(b) ): composition(f)(identity(b)) = f;
  associativity { a b c d: object }( f: hom(a)(b) )( g: hom(b)(c) )( h: hom(c)(d) ):
    composition(composition(f)(g))(h) = composition(f)(composition(g)(h));
}.

