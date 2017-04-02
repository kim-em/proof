lemma foo { α : Type } ( a b : α ) ( h : a = b ): (eq.rec (eq.refl a) h) = eq.refl b := begin

end

-- set_option pp.all true

#check eq.rec
#check prod.rec

-- eq.rec (thing : type) (p : type = type')

-- (eq.rec (C^.identity (tensor^.onObjects (tensor^.onObjects (Y^.fst), Y^.snd)))
--        (id_locked
--           (C^.Hom (tensor^.onObjects (tensor^.onObjects (Y^.fst), Y^.snd))
--              (tensor^.onObjects (tensor^.onObjects (Y^.fst), Y^.snd)) = C^.Hom
--              (tensor^.onObjects (tensor^.onObjects (Y^.fst), Y^.snd))
--              (tensor^.onObjects ((Y^.fst)^.fst, tensor^.onObjects ((Y^.fst)^.snd, Y^.snd))))
--           (eq.rec
--              (eq.rec
--                 (eq.refl
--                    (C^.Hom (tensor^.onObjects (tensor^.onObjects (Y^.fst), Y^.snd))
--                       (tensor^.onObjects (tensor^.onObjects (Y^.fst), Y^.snd))))
--                 (eq.symm pair_equality))
--              (is_strict^.associativeOnObjects ((Y^.fst)^.fst) ((Y^.fst)^.snd) (Y^.snd)))))