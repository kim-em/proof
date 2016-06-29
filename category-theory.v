Require Import CpdtTactics.
Set Implicit Arguments.

Structure Category := {
  object: Type;
  hom: object -> object -> Type;
  identity ( a: object ): hom(a)(a);
  composition { a b c: object }: hom(a)(b) -> hom(b)(c) -> hom(a)(c);
  leftIdentities { a b: object }( f: hom(a)(b) ): composition(identity(a))(f) = f;
  rightIdentities { a b: object }( f: hom(a)(b) ): composition(f)(identity(b)) = f;
  associativity { a b c d: object }( f: hom(a)(b) )( g: hom(b)(c) )( h: hom(c)(d) ):
    composition(composition(f)(g))(h) = composition(f)(composition(g)(h));
}.

Structure Functor(source target: Category) := {
  onObjects: source.(object) -> target.(object);
  onMorphisms { x y: source.(object) }:
    source.(hom)(x)(y) -> target.(hom)(onObjects(x))(onObjects(y));
  identities( x: source.(object) ):
    onMorphisms(source.(identity)(x)) = target.(identity)(onObjects(x));
  functoriality { x y z: source.(object) }( f: source.(hom)(x)(y) )( g: source.(hom)(y)(z)):
      onMorphisms(source.(composition)(f)(g)) = target.(composition)(onMorphisms(f))(onMorphisms(g))
}.

(* Can we use pattern matching in the arguments, instead of writing fst and snd everywhere? *)

Program Definition CartesianProduct(C: Category)(D: Category): Category := {|
  object := (C.(object) * D.(object)) % type;
  hom := fun p q => ((hom C (fst p) (fst q)) * (hom D (snd p) (snd q))) % type;
  identity := fun p => (identity C (fst p), identity D (snd p));
  composition := fun _ _ _ f g => (C.(composition) (fst f) (fst g), D.(composition) (snd f) (snd g));
  leftIdentities := _;
  rightIdentities := _;
  associativity := _
|}.
Next Obligation.
  pose (@leftIdentities C). (* the @ here prevents Coq from trying to fill the implicit arguments *)
  pose (@leftIdentities D).
  crush.
Defined.
Next Obligation.
  pose (@rightIdentities C).
  pose (@rightIdentities D).
  crush.
Defined.
Next Obligation.
  pose (@associativity C).
  pose (@associativity D).
  crush.
Defined.

(*
Program Definition castObject { C D: Category } ( Q: C = D ) ( a: C.(object) ) : D.(object) := _.
Program Definition castMorphism { C D: Category } ( Q: C = D ) { x y: C.(object) } ( a: C.(hom) x y ) : D.(hom) (castObject Q x) (castObject Q y) := _.
*)

(* of course, this isn't the full definition of lax; we need an associativity constraint still! *)
(* to define the strong case, we need to go back and talk about identities and isomorphisms *)

Structure LaxMonoidalCategory := {
  underlying: Category;
  tensor: Functor (CartesianProduct underlying underlying) underlying;
  associator(x y z: underlying.(object)):
    underlying.(hom)(
      (tensor.(onObjects)((tensor.(onObjects)(x,y)), z))
    )(
      (tensor.(onObjects)(x, (tensor.(onObjects)(y,z))))
    );
(*  pentagon:
    forall w x y z: underlying.(object),
    composition underlying associator(onObjects tensor (w,x))(y)(z) associator(w)(x)(onObjects tensor (y,z)) =
    composition underlying (
      composition underlying (
        ???,
        ???
      ),
      ???
    ); *)
}.

(* getting ready for strong monoidal categories *)

(*
Structure Isomorphism(category: Category)(source target: object category) := {
  map: hom category source target;
  inverse: hom category target source;
  compositionIdentity1: composition category map inverse = identity category source;
  compositionIdentity2: composition category inverse map = identity category target;
}.*)

Structure Inverse { category: Category } { source target: object category } ( map: hom category source target ) := {
  inverse: hom category target source;
  rightInverseIdentity: composition category map inverse = identity category source;
  leftInverseIdentity : composition category inverse map = identity category target;
}.
