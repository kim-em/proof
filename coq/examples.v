Require Import CpdtTactics.

Program Definition NaturalsAsCategory := {|
  object := True;
  hom := fun(a: True)(b: True) => nat;
  composition := fun _ _ _ f g => f + g;
  associativity := _
|}.
Next Obligation.
  crush.
Defined.


Program Definition DoublingAsFunctor := {|
  source := NaturalsAsCategory;
  target := NaturalsAsCategory;
  onObjects := fun(a: True) => a;
  onMorphisms := fun _ _ x => 2 * x;
  functoriality := _
|}.
Next Obligation.
  crush.
Defined.
