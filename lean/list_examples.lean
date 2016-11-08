namespace hide

inductive list (A : Type) : Type :=
| nil {} : list A
| cons : A → list A → list A

namespace list

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

variable {A : Type}

notation h :: t  := cons h t

definition append (s t : list A) : list A :=
list.rec_on s t (λ x l u, x::u)

notation s ++ t := append s t

theorem nil_append (t : list A) : nil ++ t = t := rfl

theorem cons_append (x : A) (s t : list A) : x::s ++ t = x::(s ++ t) := rfl

theorem append_nil (t : list A) : t ++ nil = t :=
list.induction_on t
  (show nil ++ nil = nil, from nil_append nil)
  (take h t,
    assume IH : t ++ nil = t,
    show h :: t ++ nil = h :: t, from
      calc
    h :: t ++ nil = h :: (t ++ nil) : cons_append h t nil
      ... = h :: t : IH)
  
theorem append_assoc (r s t : list A) : r ++ s ++ t = r ++ (s ++ t) :=
list.induction_on r
  (show nil ++ s ++ t = nil ++ (s ++ t), from
    calc
  nil ++ s ++ t = s ++ t  : rfl
    ... = nil ++ (s ++ t) : rfl)
  (take h r,
    assume IH : r ++ s ++ t = r ++ (s ++ t),
    show h :: r ++ s ++ t = h :: r ++ (s ++ t), from
      calc
    h :: r ++ s ++ t = h :: (r ++ s) ++ t : cons_append h r s
      ... = h :: (r ++ s ++ t) : cons_append h (r ++ s) t
      ... = h :: (r ++ (s ++ t)) : IH
      ... = h :: r ++ (s ++ t) : cons_append h r (s ++ t))

end list

end hide
