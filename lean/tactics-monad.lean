open tactic

variables A B : Prop

example : A → B → A ∧ B :=
by do trace "Hi, Mom!",
      trace_state
