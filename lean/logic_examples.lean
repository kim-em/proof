open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume H : p ∧ q,
    and.intro (and.right H) (and.left H))
  (assume H : q ∧ p,
    and.intro (and.right H) (and.left H))

example : p ∨ q ↔ q ∨ p :=
iff.intro
  (assume H : p ∨ q,
    or.elim H or.inr or.inl)
  (assume H : q ∨ p,
    or.elim H or.inr or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
  (assume H : (p ∧ q) ∧ r,
    and.intro (and.left (and.left H))
      (and.intro (and.right (and.left H))
        (and.right H)))
  (assume H : p ∧ (q ∧ r),
    and.intro
      (and.intro (and.left H)
        (and.left (and.right H)))
      (and.right (and.right H)))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
iff.intro
  (assume H : (p ∨ q) ∨ r,
    or.elim H
      (assume Hpq : p ∨ q,
        or.elim Hpq or.inl
          (assume Hq : q, or.inr (or.inl Hq)))
      (assume Hr : r, or.inr (or.inr Hr)))
  (assume H : p ∨ (q ∨ r),
    or.elim H
      (assume Hp : p, or.inl (or.inl Hp))
      (assume Hqr : q ∨ r,
        or.elim Hqr
          (assume Hq : q, or.inl (or.inr Hq))
          or.inr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
  (assume H : p ∧ (q ∨ r),
    have Hp : p, from and.left H,
    have Hqr : q ∨ r, from and.right H,
    or.elim Hqr
      (λ Hq, or.inl (and.intro Hp Hq))
      (λ Hr, or.inr (and.intro Hp Hr)))
  (assume H : (p ∧ q) ∨ (p ∧ r),
    or.elim H
      (assume Hpq : p ∧ q,
        and.intro (and.left Hpq)
          (or.inl (and.right Hpq)))
      (assume Hpr : p ∧ r,
        and.intro (and.left Hpr)
          (or.inr (and.right Hpr))))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
iff.intro
  (assume H : p ∨ (q ∧ r),
    or.elim H
      (λ Hp, and.intro (or.inl Hp) (or.inl Hp))
      (assume Hqr,
        and.intro
          (or.inr (and.left Hqr))
          (or.inr (and.right Hqr))))
  (assume H : (p ∨ q) ∧ (p ∨ r),
    have Hpq : p ∨ q, from and.left H,
    have Hpr : p ∨ r, from and.right H,
    or.elim Hpq or.inl
      (assume Hq : q,
        or.elim Hpr or.inl
          (assume Hr : r,
            or.inr (and.intro Hq Hr))))

-- other properties
example : (p → q → r) ↔ (p ∧ q → r) :=
iff.intro
  (assume H : p → q → r,
    (assume Hpq : p ∧ q,
      H (and.left Hpq) (and.right Hpq)))
  (assume H : p ∧ q → r,
    λ Hp, λ Hq, H (and.intro Hp Hq))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
iff.intro
  (assume H : (p ∨ q) → r,
    and.intro (λ Hp, H (or.inl Hp))
              (λ Hq, H (or.inr Hq)))
  (assume H : (p → r) ∧ (q → r),
    (assume Hpq : p ∨ q,
      or.elim Hpq (and.left H) (and.right H)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
  (assume Hpq : ¬(p ∨ q),
    show ¬p ∧ ¬q, from
    and.intro
      (assume Hp : p,
        Hpq (or.inl Hp))
      (assume Hq : q,
        Hpq (or.inr Hq)))
  (assume H : ¬p ∧ ¬q,
    have Hnp : ¬p, from and.left H,
    have Hnq : ¬q, from and.right H,
    not.intro
      (assume Hpq : p ∨ q,
        or.elim Hpq Hnp Hnq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (assume H : ¬p ∨ ¬q,
    not.intro
      (assume Hpq : p ∧ q,
        have Hp : p, from and.left Hpq,
        have Hq : q, from and.right Hpq,
        show false, from
          or.elim H
            (assume Hnp : ¬p, Hnp Hp)
            (assume Hnq : ¬q, Hnq Hq)))

example : ¬(p ∧ ¬ p) :=
not.intro
  (assume H : p ∧ ¬p,
    have Hp : p, from and.left H,
    have Hn : ¬p, from and.right H,
    show false, from Hn Hp)

example : p ∧ ¬q → ¬(p → q) :=
  (assume H : p ∧ ¬q,
    have Hp : p, from and.left H,
    have Hnq : ¬q, from and.right H,
    not.intro
      (assume Hpq : p → q,
        show false, from Hnq (Hpq Hp)))

example : ¬p → (p → q) :=
  (assume Hn : ¬p, (assume Hp : p, absurd Hp Hn))

example : (¬p ∨ q) → (p → q) :=
  (assume H : ¬p ∨ q,
    or.elim H
      (assume Hn : ¬p, (assume Hp : p, absurd Hp Hn))
      (assume Hq : q, (assume Hp : p, Hq)))

example : p ∨ false ↔ p :=
iff.intro
  (assume H : p ∨ false,
    or.elim H id false.elim)
  or.inl

example : p ∧ false ↔ false :=
iff.intro
  and.right
  (assume H : false, and.intro (false.elim H) H)

example : ¬(p ↔ ¬p) :=
not.intro
  (assume H : p ↔ ¬p,
    have Hnp: ¬p, from not.intro (λ Hp, iff.mp H Hp Hp),
    have Hp: p, from iff.mpr H Hnp,
    show false, from not.intro Hnp Hp)

example : (p → q) → (¬q → ¬p) :=
(assume H : p → q,
  (assume Hnq : ¬q,
    not.intro
      (assume Hp : p,
        Hnq (H Hp))))

-- these require classical reasoning
open classical

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  (assume H : p → r ∨ s,
  by_cases
    (assume Hp : p,
      or.elim (H Hp)
        (assume Hr : r,
          or.inl (λ Hpp : p, Hr))
        (assume Hs : s,
          or.inr (λ Hpp : p, Hs)))
    (assume Hnp : ¬p, or.inl (λ Hp : p, absurd Hp Hnp)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (assume H : ¬(p ∧ q),
  by_cases
    (assume Hp : p,
    by_cases
      (assume Hq : q, absurd (and.intro Hp Hq) H)
      (assume Hnq : ¬q, or.inr Hnq))
    (assume Hnp : ¬p, or.inl Hnp))

theorem impl_or : (p → q) → ¬p ∨ q :=
  (assume H : p → q,
    by_cases
      or.inr
      (assume Hnq : ¬q,
        by_cases
          (assume Hp : p, absurd (H Hp) Hnq)
          or.inl))

theorem or_impl : ¬p ∨ q → (p → q) :=
  (assume H : ¬p ∨ q,
    (assume Hp : p,
      or.elim H
        (λ Hnp : ¬p, absurd Hp Hnp)
        id))

theorem nimpl_and : ¬(p → q) → p ∧ ¬q :=
  (assume H : ¬(p → q),
    have Hnq : ¬q, from
      by_cases 
        (assume Hq : q, absurd (λ Hp, Hq) H)
        id,
    have Hp : p, from
      by_cases
        id
        (assume Hnp : ¬p, sorry),
    and.intro Hp Hnq)
  
example : (p → q) → (¬p ∨ q) :=
  (assume H : p → q,
    by_cases
      (assume Hp : p, or.inr (H Hp))
      (assume Hnp : ¬p, or.inl Hnp))

theorem contrapositive : (¬q → ¬p) → (p → q) :=
  (assume H : ¬q → ¬p,
    (assume Hp : p,
      or.elim (em q)
        id
        (λ Hnq : ¬q, absurd Hp (H Hnq))))

example : p ∨ ¬p :=
  em p

example : (((p → q) → p) → p) :=
  (assume Hpqp : (p → q) → p,
    by_cases 
      (assume Hp : p, Hp)
      (assume Hnp : ¬p,
        have Hnpq : ¬(p → q), from sorry,
        and.left (nimpl_and p q Hnpq)))

