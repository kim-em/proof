structure {u v} Bijection ( P : Type u ) ( Q : Type v ) :=
  ( function : P → Q )
  ( inverse  : Q → P )
  ( witness_1 : function ∘ inverse = id )
  ( witness_2 : inverse ∘ function = id )

class Finite ( α : Type ) :=
  ( n : nat )
  ( bijection : Bijection α (fin n) )

inductive Two : Type
| _0 : Two
| _1 : Two

instance Two_is_Finite : Finite Two := sorry

instance sum_is_Finite  ( P : Type ) [ Finite P ] ( Q : Type ) [ Finite Q ] : Finite ( sum P Q )  := sorry
instance prod_is_Finite ( P : Type ) [ Finite P ] ( Q : Type ) [ Finite Q ] : Finite ( prod P Q ) := sorry
instance fun_is_Finite  ( P : Type ) [ Finite P ] ( Q : Type ) [ Finite Q ] : Finite ( P → Q )   := sorry
-- finiteness for Pi and Sigma types?