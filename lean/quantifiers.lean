variables (A : Type) (p q : A → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume H : ∀ x, p x ∧ q x,
    and.intro
      (take y : A, and.left (H y))
      (take y : A, and.right (H y)))
  (assume H : (∀ x, p x) ∧ (∀ x, q x),
    take y : A,
    and.intro (and.left H y) (and.right H y))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  assume Hpq : ∀ x, p x → q x,
  assume Hp : ∀ x, p x,
  take y : A,
  Hpq y (Hp y)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  assume Hpq,
  take y : A,
  or.elim Hpq
    (λ H : (∀ x, p x), or.inl (H y))
    (λ H : (∀ x, q x), or.inr (H y))

variables (a b c : Type) (f : a → b) (g : b → c)


variable r : Prop

example : A → ((∀ x : A, r) ↔ r) :=
  assume H : A,
  iff.intro
    (assume Hr : (∀ x : A, r), Hr H)
    (assume Hr : r, take y, Hr)

open classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
iff.intro
  (assume H : ∀ x, p x ∨ r,
    by_cases or.inr
      (assume Hnr : ¬r,
        or.inl
          (take y : A,
            or.elim (H y) id (λ Hr, absurd Hr Hnr))))
  (assume H : (∀ x, p x) ∨ r,
    take y : A,
    or.elim H
      (λ Hp, or.inl (Hp y))
      or.inr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
iff.intro
  (assume H : (∀ x, r → p x),
    assume Hr : r,
    take y : A, H y Hr)
  (assume H : r → ∀ x, p x,
    take y : A,
    assume Hr : r, H Hr y)


variables (men : Type) (barber : men) (shaves : men → men → Prop)

example (H : ∀ x : men, shaves barber x ↔ ¬shaves x x) : false :=
  have Hns : ¬shaves barber barber, from
    not.intro
      (assume Hs : shaves barber barber,
        iff.mp (H barber) Hs Hs),
  have Hs : shaves barber barber, from
    iff.mpr (H barber) Hns,
  Hns Hs
