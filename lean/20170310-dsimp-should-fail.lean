structure X := ( a : Type )
definition x : X := { a := unit }
definition y : X := { a := unit } 
lemma t : x^.a = unit := begin
                           dsimp [ y ],
                           dsimp [ x ],
                           refl
                         end