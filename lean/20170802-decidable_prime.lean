
def decidable_and ( P Q : Prop ) [decidable P] [decidable Q]: decidable (P ∧ Q) :=
begin
  induction _inst_1,
  let b : ¬ (P ∧ Q) := by cc,
  exact (is_false b),
  induction _inst_2,
  let b : ¬ (P ∧ Q) := by cc,
  exact (is_false b),
  let b : P ∧ Q := by cc,
  exact (is_true b)
end

instance decidable_prime : decidable_pred prime :=
begin
  unfold decidable_pred,
  intros,
  unfold prime,
  apply @decidable_and _ _ _ _,
  
end