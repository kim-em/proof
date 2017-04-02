structure X :=
  ( a : ℕ ) ( b : ℕ )

@[reducible] def f ( x : X ) : X := ⟨ x^.b + 1, x^.a ⟩

lemma t (x : ℕ × ℕ) : (x^.fst, x^.snd) = x :=
begin
cases x,
dsimp,
trivial
end