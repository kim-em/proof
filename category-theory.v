Require Import CpdtTactics.
Obligation Tactic := crush.
Set Implicit Arguments.

Generalizable Variables a b c d.

Structure Category := {
  object: Type;
  hom: object -> object -> Type;
  identity ( a: object ): hom a a;
  composition { a b c: object }: hom a b -> hom b c -> hom a c;
  leftIdentities `( f: hom a b ): composition (identity a) f = f;
  rightIdentities `( f: hom a b ): composition f (identity b) = f;
  associativity `( f: hom a b )`( g: hom b c )`( h: hom c d ):
    composition (composition f g) h = composition f (composition g h);
}.

Program Definition NaturalsAsCategory: Category := {|
  object := True;
  hom := fun _ _ => nat;
  identity := fun _ => 0;
  composition := fun _ _ _ f g => f + g;
|}.

Set Automatic Coercions Import.
Require groups.

Program Definition SemigroupIdentity(G: groups.Semigroup): groups.SemigroupMorphism G G := {|
  groups.map := fun x => x;
|}.

Program Definition SemigroupMorphismComposition { X Y Z: groups.Semigroup } ( f: groups.SemigroupMorphism X Y ) ( g: groups.SemigroupMorphism Y Z ): groups.SemigroupMorphism X Z := {|
  groups.map := fun x => g(f x)
|}.
Next Obligation.
  pose (groups.intertwinesMultiplication _ _ f).
  pose (groups.intertwinesMultiplication _ _ g).
  crush.
Defined.

Program Definition SemigroupsAsCategory: Category := {|
  object := groups.Semigroup;
  hom := groups.SemigroupMorphism;
  identity := SemigroupIdentity;
  composition := @SemigroupMorphismComposition;
|}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Structure Functor(source target: Category) := {
  onObjects: object source -> object target;
  onMorphisms: forall `(hom source a b), hom target (onObjects a) (onObjects b);
  identities( a: object source ):
    onMorphisms (identity source a) = identity target (onObjects a);
  functoriality `( f: hom source a b )`( g: hom source b c):
      onMorphisms (composition source f g) = composition target (onMorphisms f) (onMorphisms g)
}.

Program Definition DoublingAsFunctor: Functor NaturalsAsCategory NaturalsAsCategory := {|
  onObjects := fun(a: True) => a;
  onMorphisms := fun _ _ x => 2 * x;
  functoriality := _
|}.

(* Can we use pattern matching in the arguments, instead of writing fst and snd everywhere? *)

Program Definition CartesianProduct(C: Category)(D: Category): Category := {|
  object := (object C * object D) % type;
  hom := fun p q => ((hom C (fst p) (fst q)) * (hom D (snd p) (snd q))) % type;
  identity := fun p => (identity C (fst p), identity D (snd p));
  composition := fun _ _ _ f g => (composition C (fst f) (fst g), composition D (snd f) (snd g));
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

Structure LaxMonoidalCategory := {
  underlying :> Category;
  tensor: Functor (CartesianProduct underlying underlying) underlying;
  associator(x y z: object underlying):
    underlying.(hom)(
      onObjects tensor ((onObjects tensor (x,y)), z)
    )(
      (onObjects tensor (x, onObjects tensor (y,z)))
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

Program Definition TensorProductOfNaturals: Functor (CartesianProduct NaturalsAsCategory NaturalsAsCategory) NaturalsAsCategory := {|
  onObjects := fun a => fst a;
  onMorphisms := fun _ _ p => (fst p) + (snd p);
|}.

Eval compute in onMorphisms TensorProductOfNaturals (2,7).

Program Definition NaturalsAsLaxMonoidalCategory: LaxMonoidalCategory := {|
  underlying := NaturalsAsCategory;
  tensor := TensorProductOfNaturals;
  associator := fun(x y z: True) => 0;
|}.


Structure Inverse { category: Category } { source target: object category } ( map: hom category source target ) := {
  inverse: hom category target source;
  rightInverseIdentity: composition category map inverse = identity category source;
  leftInverseIdentity : composition category inverse map = identity category target;
}.

Structure MonoidalCategory := {
  underlyingLax :> LaxMonoidalCategory;
  strength(x y z : object underlyingLax): Inverse(associator underlyingLax x y z);
}.

Program Definition NaturalsAsMonoidalCategory: MonoidalCategory := {|
  underlyingLax := NaturalsAsLaxMonoidalCategory;
  strength := _;
|}.
Next Obligation.
Admitted.

Eval compute in object NaturalsAsMonoidalCategory.