namespace tactic.interactive
  open expr tactic

  private meta def congr_aux : expr → expr → tactic unit
  | (app f₁ a₁) (app f₂ a₂) :=
  do apply ``(congr),
     swap, reflexivity <|> swap,
     congr_aux f₁ f₂
  | _ _ := try reflexivity

  /-- Given a goal of form `f a1 ... an = f' a1' ... an'`, this tactic breaks it down to subgoals
      `f = f'`, `a1 = a1'`, ... Subgoals provable by reflexivity are dispensed automatically. -/
  meta def congruence : tactic unit :=
  do ```(%%lhs = %%rhs) ← target | fail "goal is not an equality",
     congr_aux lhs rhs

  /-- Given a goal that equates two structure values, this tactic breaks it down to subgoals equating each
      pair of fields. -/
  meta def congr_struct : tactic unit :=
  do ```(%%lhs = %%rhs) ← target | fail "goal is not an equality",
     ty ← infer_type lhs,
     [ctor] ← get_constructors_for ty | fail "equated type is not a structure",
     tactic.cases lhs,
     tactic.cases rhs,
     congruence
end tactic.interactive

structure X := ( x : unit ) ( y :  unit )

lemma test1 ( a b : X ) : a = b :=
begin
  congr_struct,
    -- x y x_1 y_1 : ℕ
    -- ⊢ x = x_1

    -- x y x_1 y_1 : ℕ
    -- ⊢ y = y_1
  {
      induction x,
    induction x_1,
    reflexivity
  },
  {
    induction y,
    induction y_1,
    reflexivity
  }
  -- Great!
end

def f ( a : X ) : X := { x := a.y, y := a.x }

lemma test2 ( a : X ) : a = f (f a) :=
begin
  congr_struct,
  -- breaks because cases.lhs messes up the right hand side!
end

structure Y := ( x : nat ) ( y : nat )
def g ( x : nat ) : Y := { x := x, y := x }
def h ( a : Y ) : Y := { x := a.y, y := a.x }

lemma test3 ( x : nat ) : g 0 = h ( g 0 ) :=
begin
  congr_struct,
  
end