-- Robert Lewis solved the problem I was having here:
-- https://groups.google.com/d/msg/lean-user/iD4k4oB3794/snn158YKDwAJ
-- Just use 'sorry', not 'by sorry'!
structure S :=
  (α : Type)
  (β : unit)

structure T (c : S)

structure U (c: S) (A : c^.α)

definition V (c : S) : S :=
{
  α := T c,
  β := by sorry
}

definition W { c : S } ( F : T c ) := U (V c) F

/-
-- 15:39: type mismatch at application
--   U (V c) F
-- term
--   F
-- has type
--   T c
-- but is expected to have type
--   S.α (V c) 
-/
