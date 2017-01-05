Require Import Arith.
SearchRewrite ((_ + _) + _).
Check plus_assoc_reverse.

Definition NaturalsAsCategory := {|
  object := True;
  hom := fun(a: True)(b: True) => nat;
  composition := fun _ _ _ f g => f + g;
  associativity := fun _ _ _ _ f g h => plus_assoc_reverse(f)(g)(h);
|}.

SearchRewrite (_ * (_ + _) ).

Definition DoublingAsFunctor := {|
  source := NaturalsAsCategory;
  target := NaturalsAsCategory;
  onObjects := fun(a: True) => a;
  onMorphisms := fun _ _ x => 2 * x;
  functoriality :=  fun _ _ _ f g => Nat.mul_add_distr_l(2)(f)(g);
|}.